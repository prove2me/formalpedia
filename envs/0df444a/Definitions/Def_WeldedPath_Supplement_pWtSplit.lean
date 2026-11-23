-- Prove2me | Definitions.Def_WeldedPath_Supplement_pWtSplit
-- name    : WeldedPath_Supplement_pWtSplit
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:30:32.743615+00:00
-- url     : https://prove2.me/theorems/45ab7dfe-65fb-4f5b-a8a7-56d29dc111c1
-- title:
--   Short- and long-output contributions to the Algorithm 3.9 success probability
-- statement:
--   This module splits the success probability of Algorithm 3.9 into the two cases used in its analysis. If the output has $m$ steps, the short-output event is acceptance together with $m\le 2q+1$, and the long-output event is acceptance together with $m>2q+1$. Averaging these events over $\sigma\sim D_{\mathrm{prod}}$ and the final measurement gives $p_{\mathrm{wt}}^{\le}$ and $p_{\mathrm{wt}}^{>}$, respectively. Since the cases are disjoint and exhaustive, the module also proves
--   $$
--   p_{\mathrm{wt}}=p_{\mathrm{wt}}^{\le}+p_{\mathrm{wt}}^{>}.
--   $$
--   This is the exact probability decomposition underlying the proof of Theorem 3.12.
--
--   **Formalization Note** `pWtLe` and `pWtGt` use the same published `probOver`, algorithm, output map, and `Accepts39` predicate as `pWt`; `AcceptsLe` and `AcceptsGt` merely conjoin the corresponding length condition.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), Algorithm 3.9 and proof of Theorem 3.12, pp.23–26 (printed pp.22–25)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_WeldedPath_Supplement_pWt
import Definitions.Def_WeldedPath_Supplement_pCross

namespace WeldedPath
namespace Supplement

open QAlgorithms

/-- Acceptance of Algorithm 3.9 restricted to the short-output branch. -/
def AcceptsLe (l : ℕ) {n : ℕ} (G : WeldedInstance n)
    (σ : Equiv.Perm (Label n) × Equiv.Perm G.edges) (q : ℕ)
    (out : List (Fin 3 × Qubits (2 * n + 1))) : Prop :=
  Accepts39 l G σ q out ∧ out.length ≤ 2 * q + 1

/-- Acceptance of Algorithm 3.9 restricted to the long-output branch. -/
def AcceptsGt (l : ℕ) {n : ℕ} (G : WeldedInstance n)
    (σ : Equiv.Perm (Label n) × Equiv.Perm G.edges) (q : ℕ)
    (out : List (Fin 3 × Qubits (2 * n + 1))) : Prop :=
  Accepts39 l G σ q out ∧ 2 * q + 1 < out.length

/-- The short-output contribution to `pWt`. -/
noncomputable def pWtLe (l : ℕ) {n : ℕ} (G : WeldedInstance n)
    {W : Type*} [Fintype W] [DecidableEq W] {q : ℕ}
    (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
    (out : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W →
      List (Fin 3 × Qubits (2 * n + 1))) : ℝ :=
  G.probOver l (G.prodSupport l) A fun σ z => AcceptsLe l G σ q (out z)

/-- The long-output contribution to `pWt`. -/
noncomputable def pWtGt (l : ℕ) {n : ℕ} (G : WeldedInstance n)
    {W : Type*} [Fintype W] [DecidableEq W] {q : ℕ}
    (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
    (out : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W →
      List (Fin 3 × Qubits (2 * n + 1))) : ℝ :=
  G.probOver l (G.prodSupport l) A fun σ z => AcceptsGt l G σ q (out z)

open Classical in
/-- The two verifier branches partition acceptance. -/
theorem pWt_eq_add (l : ℕ) {n : ℕ} (G : WeldedInstance n)
    {W : Type*} [Fintype W] [DecidableEq W] {q : ℕ}
    (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
    (out : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W →
      List (Fin 3 × Qubits (2 * n + 1))) :
    pWt l G A out = pWtLe l G A out + pWtGt l G A out := by
  unfold pWt pWtLe pWtGt WeldedInstance.probOver avgOver
  rw [← add_div]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ hσ
  unfold QAlgorithms.probEvent
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases ha : Accepts39 l G σ q (out z)
  · by_cases hm : (out z).length ≤ 2 * q + 1
    · simp [AcceptsLe, AcceptsGt, ha, hm]
    · have hm' : 2 * q + 1 < (out z).length := Nat.lt_of_not_ge hm
      simp [AcceptsLe, AcceptsGt, ha, hm, hm']
  · simp [AcceptsLe, AcceptsGt, ha]

end Supplement
end WeldedPath


