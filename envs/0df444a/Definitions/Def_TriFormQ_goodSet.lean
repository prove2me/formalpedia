-- Prove2me | Definitions.Def_TriFormQ_goodSet
-- name    : TriFormQ_goodSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:52:13.415252+00:00
-- url     : https://prove2.me/theorems/79e7c48f-35cf-455c-8b60-b65e0f21a113
-- title:
--   Good set $G$ of base points
-- statement:
--   For a trilinear form $f$ on $\mathbb F_q^n$, a point $v\in\mathbb F_q^n$ is a **good base point** if it lies in
--
--   $$G=\{v\in\mathbb F_q^n:\ M(v)+q^{\mathrm{rk} f\langle v\rangle}\le 8\,q^{\mathrm{AR}(f)}\},$$
--
--   and the fiber $Z_v$ over a good base point is a **good fiber**. Good fibers have small codimension and their slices $f[u]$ have small rank (Facts 1 and 2); finding one is the first step of the identification algorithm.
--
--   **Formalization Note** $q^{\mathrm{AR}(f)}$ is a real power and $q^{\mathrm{rk}}$ a natural power of the real number $q=|\mathbb F|$.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Definition 2, p.22 (PDF p.25)

import Definitions.Def_TriFormQ_Mv
import Definitions.Def_TriFormQ_sliceV
import Definitions.Def_TriFormQ_AR

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Definition 2, p.22 (PDF p.25): "A
point v ∈ V is called a good base point if it is in the following “good set”
G := {v ∈ V : M(v) + q^{rk(f⟨v⟩)} ≤ 8q^{AR(f)}}".

**Formalization Note.** `q^{rk f⟨v⟩}` is a natural power of the real number `q = |F|`, and
`q^{AR(f)}` is the real power `Real.rpow`. -/
noncomputable def goodSet {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    (θ : TriForm F n) : Finset (Vec F n) :=
  Finset.univ.filter fun v =>
    Mv θ v + (Fintype.card F : ℝ) ^ (sliceV θ v).rank ≤ 8 * (Fintype.card F : ℝ) ^ AR θ

end TriFormQ


