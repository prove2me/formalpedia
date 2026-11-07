-- Prove2me | Definitions.Def_ShadowBootstrap_Circuit
-- name    : ShadowBootstrap_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:13.163114+00:00
-- url     : https://prove2.me/theorems/18645ef8-2cbe-408d-bb99-329185462ee0
-- title:
--   Circuits over $\{H, S, CX\}$: layers, depth, and the circuit unitary
-- statement:
--   The gates of §3.1 (p.8) are
--   $$H = \tfrac{1}{\sqrt 2}\begin{pmatrix}1&1\\1&-1\end{pmatrix},\qquad S = \begin{pmatrix}1&0\\0&i\end{pmatrix},\qquad CX = \begin{pmatrix}1&0&0&0\\0&1&0&0\\0&0&0&1\\0&0&1&0\end{pmatrix},$$
--   with $CX$ written in the basis $|00\rangle, |01\rangle, |10\rangle, |11\rangle$ with the control qubit first. A gate placed on an $n$-qubit register acts by its matrix on its qubits ($H$ or $S$ on one qubit $q$, $CX$ on a control $c$ and a target $t \ne c$) and as the identity on all other qubits.
--
--   A **layer** is a list of gates acting on pairwise disjoint sets of qubits, and a **circuit** is a list of layers $U_1, \dots, U_d$, applied in this order. Its **depth** is the number $d$ of layers and its unitary is $U = U_d \cdots U_2 U_1$. These are the circuits in which the paper counts measurement depth (Lemma 6.1, and the proof of Lemma A.2: every $k$-qubit Clifford block has an $O(k)$-depth circuit over $\{H, S, CX\}$).
--
--   **Formalization Note** Bit strings are functions $\{0,\dots,n-1\} \to \{0,1\}$; qubit $0$ is the first qubit, so the first $\ell$ qubits of the register carry the prefix $x$ of §5. Gates may act on any pair of qubits (no connectivity constraint). A circuit is *valid* when every layer has pairwise disjoint gate supports; statements about depth require validity.
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), §3.1, p.8; Lemma 6.1, p.23; Lemma A.2 and its proof, pp.34–35

import Mathlib
import Definitions.Def_ClassicalShadow_Linear_Setting

open ClassicalShadow.Linear

namespace ShadowBootstrap

/-- A gate of the paper's gate set `{H, S, CX}` (§3.1, p.8) placed on an `n`-qubit register:
`h q` and `s q` act on qubit `q`, `cx c t` is the controlled-NOT with control `c` and target
`t ≠ c`. -/
inductive Gate (n : ℕ) where
  | h (q : Fin n)
  | s (q : Fin n)
  | cx (c t : Fin n) (hct : c ≠ t)

/-- The qubits a gate acts on. -/
def Gate.support {n : ℕ} : Gate n → Finset (Fin n)
  | .h q => {q}
  | .s q => {q}
  | .cx c t _ => {c, t}

/-- The Hadamard matrix `H = (1/√2)[[1,1],[1,−1]]` (§3.1, p.8): `H_{ab} = (−1)^{ab}/√2`. -/
noncomputable def hEntry (a b : Fin 2) : ℂ :=
  ((Real.sqrt 2)⁻¹ : ℝ) * (-1 : ℂ) ^ (a.val * b.val)

/-- The phase matrix `S = [[1,0],[0,i]]` (§3.1, p.8). -/
def sEntry (a b : Fin 2) : ℂ :=
  if a = b then (if a = 1 then Complex.I else 1) else 0

/-- The controlled-NOT matrix of p.8 on the basis `|00⟩, |01⟩, |10⟩, |11⟩` with the control first:
the output pair `(a_c, a_t)` and input pair `(b_c, b_t)` give entry `1` when `a_c = b_c` and
`a_t = b_t + b_c (mod 2)`, else `0`. -/
def cxEntry (a b : Fin 2 × Fin 2) : ℂ :=
  if a.1 = b.1 ∧ a.2 = b.2 + b.1 then 1 else 0

open Classical in
/-- Cho, Kim, *Shadow bootstrapping*, arXiv:2611.06073 (version of November 2, 2026, sha256
34fab758…), §3.1, p.8: the `2ⁿ × 2ⁿ` matrix of a gate on the `n`-qubit register, the gate's
matrix on the qubits it acts on tensored with the identity on all the others. Entry `(a, b)` is
the gate entry at the restricted bit strings times `∏_{i ∉ support} δ_{a_i b_i}`. -/
noncomputable def Gate.mat {n : ℕ} : Gate n → Op n
  | .h q => fun a b => if (∀ i, i ≠ q → a i = b i) then hEntry (a q) (b q) else 0
  | .s q => fun a b => if (∀ i, i ≠ q → a i = b i) then sEntry (a q) (b q) else 0
  | .cx c t _ => fun a b =>
      if (∀ i, i ≠ c → i ≠ t → a i = b i) then cxEntry (a c, a t) (b c, b t) else 0

/-- A layer: a list of gates, valid when their supports are pairwise disjoint. -/
abbrev Layer (n : ℕ) := List (Gate n)

/-- Cho, Kim, *Shadow bootstrapping*, arXiv:2611.06073 (version of November 2, 2026, sha256
34fab758…), §3.1, p.8, Lemma 6.1 (p.23) and Lemma A.2 (pp.34–35): a measurement circuit over
`{H, S, CX}` on `n` qubits, a list of layers, the first layer applied first. Its **depth** is the
number of layers, and it is **valid** when every layer consists of gates on pairwise disjoint
qubits.

**Formalization Note** Bit strings are `Bits n = Fin n → Fin 2`; qubit `0` is the first
(most significant) qubit, so the first `ℓ` qubits of the register form the prefix `x` of §5.
Gates may act on any pair of qubits (no connectivity constraint). The unitary of a circuit is the
product of its layer matrices with the first layer rightmost; the order of the gates inside a
valid layer does not matter, since gates on disjoint qubits commute. -/
abbrev Circuit (n : ℕ) := List (Layer n)

/-- A layer is valid when its gates act on pairwise disjoint sets of qubits. -/
def Layer.IsValid {n : ℕ} (L : Layer n) : Prop :=
  L.Pairwise fun g g' => Disjoint g.support g'.support

/-- A circuit is valid when all its layers are. -/
def Circuit.IsValid {n : ℕ} (c : Circuit n) : Prop :=
  ∀ L ∈ c, Layer.IsValid L

/-- The depth of a circuit: its number of layers. -/
def depth {n : ℕ} (c : Circuit n) : ℕ := c.length

/-- The matrix of a layer: the product of its gate matrices. -/
noncomputable def Layer.mat {n : ℕ} (L : Layer n) : Op n :=
  (L.map Gate.mat).prod

/-- The unitary `U = U_d ⋯ U_2 U_1` of a circuit `[U_1, …, U_d]` (first layer applied first). -/
noncomputable def circUnitary {n : ℕ} (c : Circuit n) : Op n :=
  ((c.map Layer.mat).reverse).prod

end ShadowBootstrap


