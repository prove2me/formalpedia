-- Prove2me | Definitions.Def_AutoQMem_Lindblad_Supplement_interactionGraph
-- name    : AutoQMem_Lindblad_Supplement_interactionGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:40:52.79036+00:00
-- url     : https://prove2.me/theorems/6d55dd09-917e-4027-ad5b-788ad96ebc9b
-- title:
--   Interaction graphs, $R$-neighbourhoods and degree bounds
-- statement:
--   The **interaction graph** of a classical code $\ker H$ has the bits as vertices, two bits being adjacent if some parity check (row of $H$) acts on both. The interaction graph of a CSS code joins two qubits if some stabilizer generator (a row of $H_X$ or of $H_Z$) acts on both. For a set of qubits $A$, the **$R$-neighbourhood** $N_R(A)$ is the set of qubits at graph distance at most $R$ from $A$. A graph has **degree at most $D$** if every vertex has at most $D$ neighbours.
--
--   These notions express locality of channels (Definition 2.38), of Lindbladians (Definition 2.23) and of SPCA rules (Definition 2.40), and the bounded-degree hypothesis of Theorem 4.
--
--   **Formalization Note** Distances are extended natural numbers (`SimpleGraph.edist`), infinite between different connected components, so that disconnected qubits are never within distance $R$.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.40, p. 28 (PDF p. 30); §2.1, p. 14 (PDF p. 16); Definition 2.38, p. 27 (PDF p. 29); Theorem 4, p. 31 (PDF p. 33)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_CSSCode
open Matrix

namespace AutoQMem.Lindblad.Supplement

open AutoQMem.Lindblad

/-- **Interaction graph of a classical code `ker H`.** Drechsler, Oreg, Aharonov, *Autonomous Quantum
Memories from Classical Stochastic Processes*, arXiv:2610.05589 (PDF of 2026-11-03),
Definition 2.40, p. 28 (PDF 30): "the interaction graph of C, in which two bits are adjacent if some
parity check acts on both". Vertices are the bits `Fin n`; `i ≠ j` are adjacent iff some row `a` of
`H` has `H a i ≠ 0` and `H a j ≠ 0`. -/
def checkGraph {m n : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j => ∃ a, H a i ≠ 0 ∧ H a j ≠ 0

/-- **Interaction graph of a CSS code** (§2.1, p. 14, PDF 16, and §2.3.4): qubits `i ≠ j` are
adjacent iff some stabilizer generator (a row of `H_X` or of `H_Z`) acts on both. -/
def cssGraph {n mX mZ : ℕ} (C : CSSCode n mX mZ) : SimpleGraph (Fin n) :=
  checkGraph C.HX ⊔ checkGraph C.HZ

open Classical in
/-- **The R-neighbourhood `N_R(A)`** of a set of qubits `A`: all qubits at graph distance at most `R`
from some qubit of `A` (§2.3.4, Definition 2.38, p. 27, PDF 29).

**Formalization Note.** Distances are `SimpleGraph.edist` (`ℕ∞`, equal to `⊤` between different
connected components), not `SimpleGraph.dist` (which is `0` there); `A ⊆ N_R(A)`. -/
noncomputable def nbhd {n : ℕ} (G : SimpleGraph (Fin n)) (R : ℕ) (A : Finset (Fin n)) :
    Finset (Fin n) :=
  Finset.univ.filter fun j => ∃ i ∈ A, G.edist i j ≤ R

open Classical in
/-- **Degree bound** of a graph on `Fin n`: every vertex has at most `D` neighbours ("bounded-degree
interaction graphs", Theorem 4, p. 31, PDF 33). -/
def DegreeLE {n : ℕ} (G : SimpleGraph (Fin n)) (D : ℕ) : Prop :=
  ∀ i, (Finset.univ.filter fun j => G.Adj i j).card ≤ D

end AutoQMem.Lindblad.Supplement


