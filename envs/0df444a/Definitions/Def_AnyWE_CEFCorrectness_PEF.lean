-- Prove2me | Definitions.Def_AnyWE_CEFCorrectness_PEF
-- name    : AnyWE_CEFCorrectness_PEF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:50:49.731209+00:00
-- url     : https://prove2.me/theorems/cd2e2266-c463-4315-812a-f8597c0969a3
-- title:
--   Formulas, circuits as formulas, PEF proofs (proper/random/extension variables, four rules, length and space), EF proofs and CEF proofs (Definitions 4.25, 4.26, 4.29)
-- statement:
--   **Formulas.** Variables are of three kinds: **proper**, **random** and **extension** variables. Formulas are built from variables and the constants $\top,\bot$ with $\neg,\wedge,\vee,\oplus,\to$ and $=$ (also written $\leftrightarrow$); the size $|\varphi|$ counts variables, constants and connectives. A formula is a **tautology** if it is true under every assignment of all variables.
--
--   **Circuits as formulas (Definition 4.25).** For a circuit $C$ whose inputs are given formulas (variables, or $\top,\bot$ for hardwired bits), with an extension variable $o_j$ for gate $j$ and an output variable $y_i$ for output $i$, the gate equations $\{y:=C(\mathrm{in})\}$ are the formulas $o_j\leftrightarrow g_j(l,r)$, one per gate, and $y_i\leftrightarrow(\text{wire of output } i)$, one per output.
--
--   **PEF proofs (Definition 4.26).** Fix integers $k\ge 2$, $t,s,\ell$ and $\epsilon>0$. A $(t,s,\ell,\epsilon)$-PEF proof of a set of formulas $\Phi$ is a sequence of configurations (finite sets of formulas) $\Phi_1=\emptyset,\Phi_2,\dots,\Phi_u=\Phi$ such that each $\Phi_i$ follows from $\Phi_{i-1}$ by one rule:
--   - *Logical Inference*: for at most $k$ formulas $\theta_1,\dots,\theta_c\in\Phi_{i-1}$ and a formula $\theta$ such that $(\theta_1\wedge\dots\wedge\theta_c)\to\theta$ is a tautology, $\Phi_i=\Phi_{i-1}\cup\{\theta\}$;
--   - *Extension*: $\Phi_i=\Phi_{i-1}\cup\{e\leftrightarrow\psi\}$, where $e$ is an extension variable occurring neither in $\Phi_{i-1}$ nor in $\psi$, and $\psi$ uses only variables occurring in $\Phi_{i-1}$;
--   - *Erasure*: $\Phi_i=\Phi_{i-1}\setminus\{\theta\}$, where $\theta$ was derived by Logical Inference, or $\theta$ is an extension rule $e\leftrightarrow\psi$ for an extension variable $e$ that does not occur in $\Phi_i$;
--   - *Cryptographic Gadget Substitution*: $\Phi_{i-1}=F\cup\{y:=f(z,c)\}$ and $\Phi_i=F\cup\{y:=g(z,c')\}$ for circuits $f,g$, a vector $y$ of distinct extension variables, a vector $z$ of variables, vectors $c,c'$ of distinct random variables; $c$, $c'$ and the intermediate variables of $f$ and $g$ do not occur in $F$ (and are distinct from $y,z$); for every circuit $D$ of size at most $1/\epsilon$ and every fixed value of $z$,
--   $$\Big|\Pr_c[D(f(z,c))=1]-\Pr_{c'}[D(g(z,c'))=1]\Big|\le\epsilon;$$
--   and $|z|\le\log s$, or $|z|\le\ell$ and $|y|\le\log\ell$.
--
--   In addition the **length** $\sum_{i=1}^u\sum_{\phi\in\Phi_i}|\phi|$ is at most $t$ and the **space** $\max_i\sum_{\phi\in\Phi_i}|\phi|$ is at most $s$. A derivation from a configuration $\Phi'$ (Remark 4.28) is defined in the same way with $\Phi_1=\Phi'$.
--
--   **EF proofs.** An EF proof of a set $\Phi$ is a derivation from $\emptyset$ to $\Phi$ that has no random variables and never uses Cryptographic Gadget Substitution; its length and space are measured as above.
--
--   **CEF proofs (Definition 4.29).** For functions $t,s,\ell$ of $\lambda$, a family $\{\Phi_\lambda\}$ admits a $(t,s,\ell)$-CEF proof if there are a polynomial $u$ and one family of configuration sequences $(\Phi^{(1)}_\lambda,\dots,\Phi^{(u(\lambda))}_\lambda)$, fixed independently of $c$, such that for every constant $c>0$ and all sufficiently large $\lambda$ the sequence is a $(t(\lambda),s(\lambda),\ell(\lambda),\lambda^{-c})$-PEF proof of $\Phi_\lambda$.
--
--   These are the proof systems in which the mission's results are stated: CEF proofs certify, soundly against efficient adversaries, that a computation with honestly sampled randomness behaves correctly with overwhelming probability.
--
--   **Formalization Note.** "A constant number of formulas" in Logical Inference is the parameter $k$ (at most $k$ premises), fixed before $\lambda$; every statement of the mission holds for every $k\ge2$. Erasure's "derived from a logical inference rule" is tracked by recording, along the derivation, which formulas Logical Inference added. Extension variables introduced by Extension are fresh for the current configuration. The connectives $=$ and $\leftrightarrow$ are the same connective `iff`; hardwired bits are the constants $\top,\bot$; each output of a circuit gets its own equation $y_i\leftrightarrow(\text{wire})$.
-- source:
--   Jain, Jin, Mathialagan, SNARGs from any Witness Encryption, and More, STOC 2027 submission (manuscript sha256 9bc2f227…), p. 21, §4.1.1; p. 34, Definition 4.25; pp. 34-35, Definition 4.26 and Remarks 4.27-4.28; p. 36, Definition 4.29 and the paragraph after it

import Mathlib
import Definitions.Def_AnyWE_CEFCorrectness_Circuit
set_option autoImplicit false

/-!
# Propositional formulas, circuits as formulas, PEF, EF and CEF proofs

Jain, Jin, Mathialagan, *SNARGs from any Witness Encryption, and More*, STOC 2027 submission
(manuscript sha256 9bc2f227…), §4.1.1 p. 21 (formulas, EF), Definition 4.25 p. 34 (circuits as
formulas), Definition 4.26 and Remarks 4.27–4.28 pp. 34–35 (PEF proofs), Definition 4.29 and the
paragraph after it, p. 36 (CEF proofs; EF proofs as PEF proofs).
-/

namespace AnyWE.CEFCorrectness

/-- The three kinds of variables of PEF logic (Definition 4.26). -/
inductive VarKind
  | proper | random | ext
  deriving DecidableEq

/-- A variable: its kind and a name `(tag, idx)`. -/
structure Var where
  kind : VarKind
  tag : ℕ
  idx : ℕ
  deriving DecidableEq

/-- Propositional formulas over `→, ¬, ∧, ∨, ⊕, =` (`iff` is the connective `=`, also written
`↔`), with the constants `⊤`, `⊥` for hardwired bits. -/
inductive Formula
  | var (v : Var)
  | top
  | bot
  | not (φ : Formula)
  | and (φ ψ : Formula)
  | or (φ ψ : Formula)
  | xor (φ ψ : Formula)
  | imp (φ ψ : Formula)
  | iff (φ ψ : Formula)
  deriving DecidableEq

namespace Formula

/-- The size `|φ|`: the number of occurrences of variables, constants and connectives. -/
def size : Formula → ℕ
  | var _ => 1
  | top => 1
  | bot => 1
  | not φ => φ.size + 1
  | and φ ψ => φ.size + ψ.size + 1
  | or φ ψ => φ.size + ψ.size + 1
  | xor φ ψ => φ.size + ψ.size + 1
  | imp φ ψ => φ.size + ψ.size + 1
  | iff φ ψ => φ.size + ψ.size + 1

/-- The variables occurring in a formula. -/
def vars : Formula → Finset Var
  | var v => {v}
  | top => ∅
  | bot => ∅
  | not φ => φ.vars
  | and φ ψ => φ.vars ∪ ψ.vars
  | or φ ψ => φ.vars ∪ ψ.vars
  | xor φ ψ => φ.vars ∪ ψ.vars
  | imp φ ψ => φ.vars ∪ ψ.vars
  | iff φ ψ => φ.vars ∪ ψ.vars

/-- Truth value under an assignment of all variables. -/
def eval (ν : Var → Bool) : Formula → Bool
  | var v => ν v
  | top => true
  | bot => false
  | not φ => !φ.eval ν
  | and φ ψ => φ.eval ν && ψ.eval ν
  | or φ ψ => φ.eval ν || ψ.eval ν
  | xor φ ψ => Bool.xor (φ.eval ν) (ψ.eval ν)
  | imp φ ψ => !φ.eval ν || ψ.eval ν
  | iff φ ψ => φ.eval ν == ψ.eval ν

/-- `φ` is a tautology: true under every assignment. -/
def Tautology (φ : Formula) : Prop := ∀ ν : Var → Bool, φ.eval ν = true

/-- The conjunction `θ₁ ∧ … ∧ θ_c` (`⊤` for `c = 0`). -/
def bigAnd : List Formula → Formula
  | [] => top
  | θ :: θs => and θ (bigAnd θs)

/-- The constant formula for a hardwired bit. -/
def ofBool (c : Bool) : Formula := if c then top else bot

end Formula

/-- The formula `g(l, r)` of a gate type applied to two formulas. -/
def GateOp.formula : GateOp → Formula → Formula → Formula
  | .and, x, y => .and x y
  | .or, x, y => .or x y
  | .xor, x, y => .xor x y
  | .imp, x, y => .imp x y
  | .iff, x, y => .iff x y
  | .not, x, _ => .not x
  | .const c, _, _ => Formula.ofBool c

/-- **Circuits as formulas (Definition 4.25).** The gate equations `{out := C(in)}` of a circuit
whose inputs are the formulas `inp` (variables, or constants for hardwired bits), whose gate `j`
has the extension variable `iv j`, and whose output `i` is named `outv i`: one equation
`iv j ↔ g_j(l, r)` per gate and one equation `outv i ↔ (wire of output i)` per output.
An undefined wire reads `⊥`, as in `Circuit.eval`. -/
def gateEqs {a b : ℕ} (C : Circuit a b) (inp : Fin a → Formula) (iv : ℕ → Var)
    (outv : Fin b → Var) : Finset Formula :=
  let ref : ℕ → ℕ → Formula := fun j w =>
    if h : w < a then inp ⟨w, h⟩ else if w < a + j then .var (iv (w - a)) else .bot
  (Finset.univ.image fun j : Fin C.gates.length =>
      Formula.iff (.var (iv j.val))
        ((C.gates.get j).op.formula (ref j.val (C.gates.get j).l) (ref j.val (C.gates.get j).r))) ∪
    Finset.univ.image fun i : Fin b =>
      Formula.iff (.var (outv i)) (ref C.gates.length (C.out i))

/-- The canonical names of computation number `τ` in an assertion: gate `j` is the extension
variable `(ext, 2τ, j)` and output `i` is `(ext, 2τ+1, i)`. -/
def compOut (τ i : ℕ) : Formula := .var ⟨.ext, 2 * τ + 1, i⟩

/-- The gate equations of computation number `τ` with the canonical names. -/
def compEqs {a b : ℕ} (τ : ℕ) (C : Circuit a b) (inp : Fin a → Formula) : Finset Formula :=
  gateEqs C inp (fun j => ⟨.ext, 2 * τ, j⟩) (fun i => ⟨.ext, 2 * τ + 1, i.val⟩)

/-- Hardwired bits as constant formulas. -/
def constIn {n : ℕ} (x : Bits n) : Fin n → Formula := fun i => Formula.ofBool (x i)

/-- The variables `(κ, tag, 0), …, (κ, tag, n-1)` as formulas. -/
def varsIn (n : ℕ) (κ : VarKind) (tag : ℕ) (off : ℕ := 0) : Fin n → Formula :=
  fun i => .var ⟨κ, tag, off + i.val⟩

/-- The variables of a configuration. -/
def cfgVars (Φ : Finset Formula) : Finset Var := Φ.biUnion Formula.vars

/-- The size `∑_{ϕ ∈ Φ} |ϕ|` of a configuration. -/
def cfgSize (Φ : Finset Formula) : ℕ := Φ.sum Formula.size

/-- **Cryptographic Gadget Substitution (Definition 4.26).** `Φ = F ∪ {y := f(z, c)}` and
`Φ' = F ∪ {y := g(z, c')}`: `y` extension variables, `z` arbitrary variables, `c, c'` random
variables; `c, c'` and the intermediate variables of `f, g` do not occur in `F`; every circuit `D`
of size at most `1/ϵ` distinguishes `f(z, c)` from `g(z, c')` with advantage at most `ϵ` for every
fixed `z`; and `|z| ≤ log s` or (`|z| ≤ ℓ` and `|y| ≤ log ℓ`). -/
def GadgetSub (s ℓ : ℕ) (ϵ : ℝ) (Φ Φ' F : Finset Formula) : Prop :=
  ∃ (dz dc dc' dy : ℕ) (f : Circuit (dz + dc) dy) (g : Circuit (dz + dc') dy)
    (z : Fin dz → Var) (c : Fin dc → Var) (c' : Fin dc' → Var) (y : Fin dy → Var)
    (ivf ivg : ℕ → Var),
    Φ = F ∪ gateEqs f (Fin.append (fun i => .var (z i)) (fun i => .var (c i))) ivf y ∧
    Φ' = F ∪ gateEqs g (Fin.append (fun i => .var (z i)) (fun i => .var (c' i))) ivg y ∧
    (∀ i, (y i).kind = .ext) ∧ Function.Injective y ∧
    (∀ i, (c i).kind = .random) ∧ Function.Injective c ∧
    (∀ i, (c' i).kind = .random) ∧ Function.Injective c' ∧
    (∀ i i', c i ≠ z i') ∧ (∀ i i', c' i ≠ z i') ∧ (∀ i i', y i ≠ z i') ∧
    (∀ j < f.size, (ivf j).kind = .ext) ∧ Set.InjOn ivf {j | j < f.size} ∧
    (∀ j < g.size, (ivg j).kind = .ext) ∧ Set.InjOn ivg {j | j < g.size} ∧
    (∀ j < f.size, (∀ i, ivf j ≠ y i) ∧ ∀ i, ivf j ≠ z i) ∧
    (∀ j < g.size, (∀ i, ivg j ≠ y i) ∧ ∀ i, ivg j ≠ z i) ∧
    (∀ i, c i ∉ cfgVars F) ∧ (∀ i, c' i ∉ cfgVars F) ∧
    (∀ j < f.size, ivf j ∉ cfgVars F) ∧ (∀ j < g.size, ivg j ∉ cfgVars F) ∧
    (∀ D : Circuit dy 1, (D.size : ℝ) ≤ 1 / ϵ → ∀ zv : Bits dz,
      |prob dc (fun cv => D.eval (f.eval (Fin.append zv cv)) 0 = true) -
        prob dc' (fun cv => D.eval (g.eval (Fin.append zv cv)) 0 = true)| ≤ ϵ) ∧
    (2 ^ dz ≤ s ∨ (dz ≤ ℓ ∧ 2 ^ dy ≤ ℓ))

/-- One step of a PEF derivation (Definition 4.26) between configurations `p = (Φ, M)` and
`p' = (Φ', M')`, where `M ⊆ Φ` records the formulas derived by Logical Inference (needed by
Erasure). Logical Inference uses at most `k` premises. Extension introduces `e ↔ ψ` with `e` an
extension variable not occurring in `Φ` or `ψ` and `ψ` using only variables of `Φ`. Erasure removes
a formula derived by Logical Inference, or an extension rule `e ↔ ψ` whose `e` no longer occurs.
Gadget Substitution is allowed iff `gadget = true`. -/
def PEFStep (k s ℓ : ℕ) (ϵ : ℝ) (gadget : Bool)
    (p p' : Finset Formula × Finset Formula) : Prop :=
  (∃ prem : List Formula, prem.length ≤ k ∧ (∀ θ ∈ prem, θ ∈ p.1) ∧
      ∃ θ : Formula, (Formula.imp (Formula.bigAnd prem) θ).Tautology ∧
        p'.1 = insert θ p.1 ∧ p'.2 = insert θ p.2) ∨
  (∃ (e : Var) (ψ : Formula), e.kind = .ext ∧ e ∉ cfgVars p.1 ∧ e ∉ ψ.vars ∧
      ψ.vars ⊆ cfgVars p.1 ∧ p'.1 = insert (.iff (.var e) ψ) p.1 ∧ p'.2 = p.2) ∨
  (∃ θ ∈ p.1, p'.1 = p.1.erase θ ∧ p'.2 = p.2.erase θ ∧
      (θ ∈ p.2 ∨ ∃ (e : Var) (ψ : Formula), θ = .iff (.var e) ψ ∧ e.kind = .ext ∧
        e ∉ cfgVars p'.1)) ∨
  (gadget = true ∧ ∃ F : Finset Formula, GadgetSub s ℓ ϵ p.1 p'.1 F ∧ p'.2 = p.2 ∩ F)

/-- A valid derivation `Φ₁, …, Φ_u` from `start` to `target` (Remarks 4.27–4.28): each step is a
rule of Definition 4.26 for some record `M_i` of inference-derived formulas, `M₁ = ∅`. -/
def ValidDeriv (k s ℓ : ℕ) (ϵ : ℝ) (gadget : Bool) (start target : Finset Formula)
    (cs : List (Finset Formula)) : Prop :=
  ∃ ms : List (Finset Formula), ms.length = cs.length ∧ cs.head? = some start ∧
    ms.head? = some ∅ ∧ cs.getLast? = some target ∧
    List.IsChain (PEFStep k s ℓ ϵ gadget) (cs.zip ms)

/-- Length `∑_i ∑_{ϕ ∈ Φ_i} |ϕ|` of a derivation. -/
def derivLength (cs : List (Finset Formula)) : ℕ := (cs.map cfgSize).sum

/-- Space `max_i ∑_{ϕ ∈ Φ_i} |ϕ|` of a derivation. -/
def derivSpace (cs : List (Finset Formula)) : ℕ := (cs.map cfgSize).foldr max 0

/-- **(t, s, ℓ, ϵ)-PEF proof from `start` to `target` (Definition 4.26, Remarks 4.27–4.28)**, with
at most `k` premises per Logical Inference. -/
def IsPEFProofFrom (k t s ℓ : ℕ) (ϵ : ℝ) (start target : Finset Formula)
    (cs : List (Finset Formula)) : Prop :=
  ValidDeriv k s ℓ ϵ true start target cs ∧ derivLength cs ≤ t ∧ derivSpace cs ≤ s

/-- A `(t, s, ℓ, ϵ)`-PEF proof of the set `Φ` (from `Φ₁ = ∅`). -/
def IsPEFProof (k t s ℓ : ℕ) (ϵ : ℝ) (Φ : Finset Formula) (cs : List (Finset Formula)) : Prop :=
  IsPEFProofFrom k t s ℓ ϵ ∅ Φ cs

/-- An **EF proof** of the set `Φ` (p. 36): a PEF derivation from `∅` with no random variables that
never uses Cryptographic Gadget Substitution; its length and space are `derivLength`, `derivSpace`. -/
def IsEFProof (k : ℕ) (Φ : Finset Formula) (cs : List (Finset Formula)) : Prop :=
  ValidDeriv k 0 0 1 false ∅ Φ cs ∧ ∀ Ψ ∈ cs, ∀ v ∈ cfgVars Ψ, v.kind ≠ .random

/-- **(t, s, ℓ)-CEF proof (Definition 4.29)** of a family `{Φ_λ}`: one polynomial `u` and one family
of configuration sequences of lengths `u(λ)`, fixed before `c`, such that for every constant
`c > 0` and all sufficiently large `λ` the sequence is a `(t(λ), s(λ), ℓ(λ), λ^{-c})`-PEF proof of
`Φ_λ`. -/
def CEFProof (k : ℕ) (t s ℓ : ℕ → ℕ) (Φ : ℕ → Finset Formula) : Prop :=
  ∃ (u : Polynomial ℕ) (cs : ℕ → List (Finset Formula)), (∀ lam, (cs lam).length = u.eval lam) ∧
    ∀ c : ℝ, 0 < c → ∀ᶠ lam in Filter.atTop,
      IsPEFProof k (t lam) (s lam) (ℓ lam) ((lam : ℝ) ^ (-c)) (Φ lam) (cs lam)

end AnyWE.CEFCorrectness


