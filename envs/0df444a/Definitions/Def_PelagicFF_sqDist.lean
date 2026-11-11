-- Prove2me | Definitions.Def_PelagicFF_sqDist
-- name    : PelagicFF_sqDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:54:45.595265+00:00
-- url     : https://prove2.me/theorems/82993633-3c96-47d9-9ca6-2e61aa3d34c7
-- title:
--   Squared distance and inner product on $\{-1,1\}^\iota$
-- statement:
--   For $w,u\in\{-1,1\}^\iota$ ($\iota$ a finite coordinate set),
--   $$\|w-u\|_2^2=\sum_{i\in\iota}(w_i-u_i)^2,\qquad \langle w,u\rangle=\sum_{i\in\iota}w_iu_i .$$
--
--   These are the distances and inner products of the coupling lemmas (Lemmas 3.1, 3.3, 3.7) and of Lemma 4.3.
--
--   **Formalization Note** Points are `ι → Bool`, coordinate $b$ read as `sign b`; the module also defines `signInner`.
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), Lemma 3.1, p.18; Lemma 4.3, p.28

import Mathlib
import Definitions.Def_Cotype

open OAI.Cotype

namespace PelagicFF

/-- The squared Euclidean distance `‖W − U‖₂² = ∑ᵢ (Wᵢ − Uᵢ)²` of two points of `{−1,1}^ι`
encoded as `ι → Bool` (bit `b` stands for `sign b`, `sign false = 1`, `sign true = −1`).
arXiv:2610.05585 (held version, sha256 4564aef3…), Lemma 3.1, p.18. -/
noncomputable def sqDist {ι : Type} [Fintype ι] (w u : ι → Bool) : ℝ :=
  ∑ i, (sign (w i) - sign (u i)) ^ 2

/-- The inner product `⟨X, Y⟩ = ∑ᵢ XᵢYᵢ` of two points of `{−1,1}^ι` encoded as `ι → Bool`.
arXiv:2610.05585 (held version, sha256 4564aef3…), Lemma 4.3, p.28. -/
noncomputable def signInner {ι : Type} [Fintype ι] (x y : ι → Bool) : ℝ :=
  ∑ i, sign (x i) * sign (y i)

end PelagicFF


