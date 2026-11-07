-- Prove2me | Definitions.Def_ApproxGKR_LayeredCircuit
-- name    : ApproxGKR_LayeredCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:00.009012+00:00
-- url     : https://prove2.me/theorems/15ad4aec-f5ff-4142-a8a6-2cb30952b500
-- title:
--   Layered arithmetic circuits over $\mathbb C$, gate values, wiring predicates and admissible extensions
-- statement:
--   A **layered arithmetic circuit over $\mathbb C$** of depth $L\ge1$ has its single output at layer $0$ and its inputs at layer $L$. Fix $h=2^t\ge2$ and $H=\Omega_h$; the gates of layer $i$ are labelled by $H^{m_i}$, with $m_0=0$ (the output's empty label) and $m_i\ge1$ for $1\le i\le L$. After padding, every label $g$ of a layer $i<L$ is a gate that adds or multiplies the values of an ordered pair of children $(u,v)$ in layer $i+1$. The input is a list of the $n$ input gates (including constant gates) as pairs (label, Gaussian dyadic value); unused labels of layer $L$ have value $0$.
--
--   The **exact gate values** $V_i(g)$ are computed over $\mathbb C$ from layer $L$ toward layer $0$, and $C(x)=V_0(())$. The module also defines
--   1. the shape quantities $k_i=m_i+2m_{i+1}$, $k=\sum_{i<L}k_i$, $m=\max_{i\le L}m_i$, $S=\sum_{i\le L}h^{m_i}$, $D=\delta+h-1$;
--   2. the extensions $\widetilde V_i$ of the gate values;
--   3. the **wiring predicates** $\mathrm{add}_i(g,u,v)$, $\mathrm{mult}_i(g,u,v)$: $1$ if $g$ is a gate of that type with ordered children $u,v$, else $0$;
--   4. **admissible extensions**: polynomials in the $k_i$ variables $(g,u,v)$ of degree at most $\delta$ in each variable, agreeing with the wiring predicate on $H^{m_i}\times H^{m_{i+1}}\times H^{m_{i+1}}$, with $\|\cdot\|_1\le B_W$ (any such polynomial, not only the unique one of degree below $h$);
--   5. `ValidInputs` (distinct labels of layer $L$) and `GateBound` (every exact gate value at every layer has modulus at most $B_V$).
--
--   **Formalization Note** Labels are tuples of root indices. The gate map is total on all labels of layers $i<L$ (the paper's padded circuit); its values for $i\ge L$ are unused. The variables of an extension are ordered $g$, then $u$, then $v$.
-- source:
--   Das, Gupta, Mondal, More, Delegating Computation with Approximate Arithmetic: Interactive Proofs for Wizards (manuscript, sha256 78b2a36b…), §C.1, pp.29–30, 32

import Mathlib
import Definitions.Def_ApproxGKR_root
import Definitions.Def_ApproxGKR_mvNorm1
import Definitions.Def_ApproxGKR_lagrangeBasis
import Definitions.Def_ApproxGKR_dyadicVal

namespace ApproxGKR

/-- The two gate types of a layered arithmetic circuit over `ℂ`. -/
inductive GateType where
  | add
  | mult
  deriving DecidableEq

/-- A **layered arithmetic circuit over `ℂ`** after padding, with labels in `H^{m_i}`.

Das, Gupta, Mondal, More, *Delegating Computation with Approximate Arithmetic* (manuscript,
sha256 78b2a36b…), §C.1, pp.29–30: "Let `C` be a layered arithmetic circuit of depth `L ≥ 1`,
with the single output at layer 0 and the inputs at layer `L`. Each noninput gate adds or
multiplies the values of two gates in the next layer, called its children." "fix a power of two
`h ≥ 2`"; "We set `m₀ = 0` for the output's empty label and require `mᵢ ≥ 1` for `i > 0`."
"Layer `i` then has `h^{mᵢ}` labels".

**Formalization Note**
* `h = 2^t` with `t ≥ 1`; a label of layer `i` is a tuple `Fin (m i) → Fin h` of root indices
  (index `a` stands for `exp(2πia/h)`).
* After padding every label of layers `0, …, L−1` is a gate (the paper's convention: unused
  labels get zero gates, copies are additions of zero), so `gate i g` gives the type and the
  ordered pair `(u, v)` of children (possibly `u = v`) of every label `g` of layer `i`. Its values
  for `i ≥ L` are never used.
* `m` is read on `0, …, L`; its values beyond `L` are irrelevant. -/
structure LayeredCircuit where
  /-- the depth `L` -/
  L : ℕ
  /-- `h = 2^t` -/
  t : ℕ
  /-- `m i` coordinates in a label of layer `i` -/
  m : ℕ → ℕ
  /-- type and ordered children of the gate with label `g` at layer `i < L` -/
  gate : (i : ℕ) → (Fin (m i) → Fin (2 ^ t)) →
    GateType × (Fin (m (i + 1)) → Fin (2 ^ t)) × (Fin (m (i + 1)) → Fin (2 ^ t))
  one_le_L : 1 ≤ L
  one_le_t : 1 ≤ t
  m_zero : m 0 = 0
  one_le_m : ∀ i, 1 ≤ i → i ≤ L → 1 ≤ m i

namespace LayeredCircuit

variable (C : LayeredCircuit)

/-- The label alphabet size `h = 2^t ≥ 2`. -/
abbrev h : ℕ := 2 ^ C.t

/-- Labels of layer `i`: `H^{m_i}`, as index tuples. -/
abbrev Label (i : ℕ) : Type := Fin (C.m i) → Fin C.h

/-- `k_i = m_i + 2m_{i+1}` (p.30), the number of sum-check rounds at layer `i`. -/
abbrev ki (i : ℕ) : ℕ := C.m i + C.m (i + 1) + C.m (i + 1)

/-- `k = Σ_{i=0}^{L−1} k_i` (p.30), the total number of rounds. -/
def k : ℕ := ∑ i ∈ Finset.range C.L, C.ki i

/-- `m = max_i m_i` over the layers `0, …, L` (p.30). -/
def mMax : ℕ := (Finset.range (C.L + 1)).sup C.m

/-- The size `S = Σ_{i=0}^{L} h^{m_i}` after padding (p.30). -/
def size : ℕ := ∑ i ∈ Finset.range (C.L + 1), C.h ^ C.m i

/-- `D = δ + h − 1` (p.30), the degree bound of the round polynomials. -/
def Dpar (δ : ℕ) : ℕ := δ + C.h - 1

end LayeredCircuit

/-- The input of a circuit: the list of the `n` input gates (including constant gates) as pairs
(label, value), the label given by its list of root indices and the value a Gaussian dyadic.
"The values of the `n` input gates, including constant gates, are at known labels; unused labels
in the input layer have value zero. Their real and imaginary parts have finite binary
expansions." (p.30) -/
abbrev InputList : Type := List (List ℕ × GaussDyadic)

/-- The value at a label `g` given by an input list: the sum of the values listed under the index
list of `g` (zero when the label is not listed). For a list with distinct labels
(`ValidInputs`) it is the value of the input gate at `g`. -/
noncomputable def inputValueAt {h m : ℕ} (x : InputList) (g : Fin m → Fin h) : ℂ :=
  ((x.filter (fun e => decide (e.1 = List.ofFn (fun j => (g j).val)))).map
    (fun e => dyadicVal e.2)).sum

/-- The exact gate values `V_i(g)`, computed over `ℂ` from the input layer `L` toward layer `0`
("Computation therefore proceeds from layer `L` toward layer 0", p.30; "Throughout, `C(x)`
denotes the exact output, before numerical approximation", p.30). For `i > L` the value is `0`
(never used). -/
noncomputable def value (C : LayeredCircuit) (x : InputList) (i : ℕ) (g : C.Label i) : ℂ :=
  if _hi : i < C.L then
    match C.gate i g with
    | (GateType.add, u, v) => value C x (i + 1) u + value C x (i + 1) v
    | (GateType.mult, u, v) => value C x (i + 1) u * value C x (i + 1) v
  else if i = C.L then inputValueAt x g else 0
termination_by C.L - i
decreasing_by all_goals omega

/-- The exact output `C(x) = V₀(())` of the circuit (p.30). -/
noncomputable def output (C : LayeredCircuit) (x : InputList) : ℂ :=
  value C x 0 (fun j => Fin.elim0 (Fin.cast C.m_zero j))

/-- The extension `Ṽ_i` of the gate values of layer `i` (eq. (C.1), p.30). -/
noncomputable def Vt (C : LayeredCircuit) (x : InputList) (i : ℕ) :
    MvPolynomial (Fin (C.m i)) ℂ :=
  extension (h := C.h) (value C x i)

/-- The wiring predicate `add_i(g,u,v)` (for `ty = add`) or `mult_i(g,u,v)` (for `ty = mult`):
`1` if `g` is a gate of that type with ordered children `u, v`, and `0` otherwise (p.30). -/
def wire (C : LayeredCircuit) (i : ℕ) (ty : GateType) (g : C.Label i)
    (u v : C.Label (i + 1)) : ℂ :=
  if C.gate i g = (ty, u, v) then 1 else 0

/-- The point `(g, u, v) ∈ ℂ^{k_i}` of a label triple, coordinates in the order `g, u, v`. -/
noncomputable def wirePoint (C : LayeredCircuit) {i : ℕ} (g : C.Label i)
    (u v : C.Label (i + 1)) : Fin (C.ki i) → ℂ :=
  Fin.append (Fin.append (labelPoint g) (labelPoint u)) (labelPoint v)

/-- A family of polynomial extensions `add~_i`, `mult~_i` of the wiring predicates, in the
`k_i = m_i + 2m_{i+1}` variables `(g, u, v)`. -/
abbrev ExtFamily (C : LayeredCircuit) : Type :=
  (i : ℕ) → GateType → MvPolynomial (Fin (C.ki i)) ℂ

/-- An **admissible extension** of the wiring predicate of type `ty` at layer `i`: individual
degree at most `δ`, agreement with the predicate on `H^{m_i} × H^{m_{i+1}} × H^{m_{i+1}}`, and
coefficient norm at most `B_W`.

Das, Gupta, Mondal, More (manuscript, sha256 78b2a36b…), §C.1, p.30: "Let `add~ᵢ`, `mult~ᵢ` be
extensions of these indicators, each of degree at most a nonnegative integer `δ` in every
variable. They need to agree with the indicators only on `H^{mᵢ} × H^{mᵢ₊₁} × H^{mᵢ₊₁}`." "we also
allow higher-degree extensions"; p.32: "`∥add~ᵢ∥₁, ∥mult~ᵢ∥₁ ≤ B_W`".

**Formalization Note** No uniqueness or degree-below-`h` condition: every such polynomial is
admissible, as on the page. -/
def IsAdmissibleExt (C : LayeredCircuit) (δ BW : ℕ) (i : ℕ) (ty : GateType)
    (P : MvPolynomial (Fin (C.ki i)) ℂ) : Prop :=
  (∀ v, P.degreeOf v ≤ δ) ∧
  (∀ (g : C.Label i) (u v : C.Label (i + 1)),
    MvPolynomial.eval (wirePoint C g u v) P = wire C i ty g u v) ∧
  mvNorm1 P ≤ BW

/-- The input list describes `n` input gates at distinct valid labels of layer `L` ("The values of
the `n` input gates … are at known labels", p.30). -/
def ValidInputs (C : LayeredCircuit) (x : InputList) : Prop :=
  (x.map Prod.fst).Nodup ∧ ∀ e ∈ x, e.1.length = C.m C.L ∧ ∀ a ∈ e.1, a < C.h

/-- Every exact gate value, at every layer `0, …, L` and label, has modulus at most `B_V`
("every exact gate value has modulus at most `B_V`", p.32). -/
def GateBound (C : LayeredCircuit) (x : InputList) (BV : ℕ) : Prop :=
  ∀ i ≤ C.L, ∀ g : C.Label i, ‖value C x i g‖ ≤ BV

end ApproxGKR


