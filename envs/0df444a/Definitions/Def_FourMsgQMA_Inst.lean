-- Prove2me | Definitions.Def_FourMsgQMA_Inst
-- name    : FourMsgQMA_Inst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:32:04.919455+00:00
-- url     : https://prove2.me/theorems/e2738fd6-7633-4879-8e86-d64f648da538
-- title:
--   NP ∘ batchQMA instances $u=(C,X)$ and the promise sets $L^C_{\mathrm{yes}}$, $L^C_{\mathrm{no}}$
-- statement:
--   An **NP ∘ batchQMA instance** $u=(C,X)$ consists of a circuit policy $C$ on $k$ bits with $s$ gates and a batch $X=(x_1,\dots,x_k)$ of instance strings. It is **admissible** when $k\ge1$ and $C$ is canonical.
--
--   For a promise problem $L$ (Definition 3.1),
--   $$
--   L^C_{\mathrm{yes}}=\{X:\exists y\in\{0,1\}^k,\ C(y)=1\wedge\forall i\in[k],\ (y_i=1\Rightarrow x_i\in L_{\mathrm{yes}})\},
--   $$
--   $$
--   L^C_{\mathrm{no}}=\{X:\forall y\in\{0,1\}^k,\ C(y)=1\Rightarrow\exists i\in[k],\ y_i=1\wedge x_i\in L_{\mathrm{no}}\}.
--   $$
--   A zero in $y$ leaves the coordinate unused; NOT gates constrain the selection and never certify non-membership (Remark 3.3).
--
--   The module also fixes the encoding of $u$ as a bit string (its size $|u|$), the batch cost $t(X)=\max_i t_L(x_i)$, and the classical part $(y,a)$ of the honest resource, $a$ the wire values of $C$ on $y$.
--
--   **Formalization Note** Pinned-down version (operator request): $t(X)$ replaces the paper's $T$. Both promise sets are restricted to admissible instances; the sets are disjoint (proved in the sanity file).
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), Definition 3.1 and Remark 3.3, p.10 (PDF 12); §3.1, p.9; §5.1, pp.34, 36 (PDF 36, 38)

import Mathlib
import Definitions.Def_FourMsgQMA_WQ
import Definitions.Def_FourMsgQMA_PolicyCircuit

namespace FourMsgQMA

/-!
Goyal, Koppula, STOC 2027 submission (sha256 6c523d45…), Definition 3.1 (p.10, PDF 12), §3.1
(p.9) and §5.1 (pp.34, 36): NP ∘ batchQMA instances `u = (C, X)`, their promise sets, the
classical part of the honest resource and the resource parameters.
-/

open QAlgorithms.Complexity TightPQRepetition.Main

/-- An NP ∘ batchQMA instance `u = (C, X)`: a circuit policy `C` on `k` bits with `s` gates and a
batch `X = (x_1, …, x_k)` of instance strings (`x_i` is `X ⟨i - 1, _⟩`). -/
structure Inst where
  /-- The batch size `k`. -/
  k : ℕ
  /-- The number `s` of gates of the policy. -/
  s : ℕ
  /-- The policy `C`. -/
  C : PolicyCircuit k s
  /-- The batch `X`. -/
  X : Fin k → Str

/-- Admissible instances: `k ≥ 1` (§3.1, p.9: "We take `k, T ≥ 1` and `s ≥ 0`") and a canonically
encoded policy (Definition 3.1, Figure 4; "Invalid … circuit descriptions cause rejection", p.9). -/
def Inst.Admissible (u : Inst) : Prop := 1 ≤ u.k ∧ u.C.IsCanonical

/-- The encoding of `u = (C, X)` as one bit string: the circuit table followed by the batch. -/
def Inst.encode (u : Inst) : Bits := pack (u.C.encode :: List.ofFn u.X)

/-- The size `|u|` of an instance. -/
def Inst.size (u : Inst) : ℕ := u.encode.length

/-- Definition 3.1 (p.10): the yes-promise `L^C_yes = {X : ∃ y ∈ {0,1}^k, C(y) = 1 ∧ ∀ i ∈ [k],
(y_i = 1 ⇒ x_i ∈ L_yes)}`, over admissible instances. -/
def yesSet (L : PromiseProblem) : Set Inst :=
  {u | u.Admissible ∧ ∃ y : Fin u.k → Bool, u.C.eval y = true ∧ ∀ i, y i = true → u.X i ∈ L.yes}

/-- Definition 3.1 (p.10): the no-promise `L^C_no = {X : ∀ y ∈ {0,1}^k, C(y) = 1 ⇒ ∃ i ∈ [k],
y_i = 1 ∧ x_i ∈ L_no}`, over admissible instances. A NOT gate constrains the selection; it never
certifies non-membership (Remark 3.3). -/
def noSet (L : PromiseProblem) : Set Inst :=
  {u | u.Admissible ∧ ∀ y : Fin u.k → Bool, u.C.eval y = true → ∃ i, y i = true ∧ u.X i ∈ L.no}

/-- The local resource bound `t(X) = max_i t_L(x_i)` of the batch, used in place of the paper's `T`
(§3.1, p.9). -/
def batchCost (F : QMAFamily) (u : Inst) : ℕ :=
  Finset.univ.sup fun i : Fin u.k => localCost F (u.X i)

/-- The classical part of the honest resource (Definition 3.1, p.10; §5.1, p.36: "an authorized
vector `y`, its policy wire values"): `y` and the wire-value array `a` of `C` on `y`, encoded. -/
def Inst.classicalWitness (u : Inst) (y : Fin u.k → Bool) : Bits :=
  pack [List.ofFn y, u.C.wireValues y]

end FourMsgQMA


