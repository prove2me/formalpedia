-- Prove2me | Definitions.Def_HybridXorLift_fibreAvg
-- name    : HybridXorLift_fibreAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:13:44.132896+00:00
-- url     : https://prove2.me/theorems/83918fa3-4e3b-421c-a309-ddad32071a77
-- title:
--   Average over a parity fibre $\mathbb E_{x \in \sigma^{-1}(z)}$
-- statement:
--   For an outer string $z \in \{0,1\}^n$ and a function $g$ of physical inputs, the **fibre average** is the uniform average
--   $$
--   \mathbb E_{x \in \sigma^{-1}(z)}\, g(x) = \frac{1}{|\sigma^{-1}(z)|} \sum_{x : \sigma(x) = z} g(x)
--   $$
--   over the parity fibre of $z$ ("An expectation over a finite set is uniform unless we say otherwise").
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §2.3, p.10 (PDF p.12); §2, p.9 (PDF p.11)

import Definitions.Def_HybridXorLift_outer

namespace HybridXorLift

/-- The uniform average `E_{x ∈ σ⁻¹(z)} g(x)` over the parity fibre of an outer string `z`
(Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §2.3, p.10 (PDF p.12), and §2: "An expectation over a finite set is uniform unless we say
otherwise", p.9 (PDF p.11)). The fibre has `2^{n(r−1)}` elements for `r ≥ 1`. -/
noncomputable def fibreAvg {n r : ℕ} (z : Fin n → Bool) (g : (Fin n × Fin r → Bool) → ℝ) : ℝ :=
  (∑ x ∈ Finset.univ.filter (fun x => outer x = z), g x) /
    ((Finset.univ.filter (fun x : Fin n × Fin r → Bool => outer x = z)).card : ℝ)

end HybridXorLift


