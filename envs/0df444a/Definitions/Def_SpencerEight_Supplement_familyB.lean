-- Prove2me | Definitions.Def_SpencerEight_Supplement_familyB
-- name    : SpencerEight_Supplement_familyB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:51:20.990081+00:00
-- url     : https://prove2.me/theorems/1a8491c2-36a1-47ae-acc5-3277017a34e3
-- title:
--   Members $P_{x,x^3+x}$ of the family $\mathcal B_k$
-- statement:
--   Fix a basis $b_1,\dots,b_k$ of $\mathrm{GF}(2^k)$ over $\mathbb F_2$ and let $\varphi:\mathrm{GF}(2^k)\to\mathbb F_2^k$ be its coordinate map. For $x\in\mathrm{GF}(2^k)$,
--   $$
--   P_x:=P_{\varphi(x),\,\varphi(x^3+x)},
--   $$
--   with $x^3+x$ computed in $\mathrm{GF}(2^k)$. With $b$ self-dual this is the member $P_{x,x^3+x}$ of $\mathcal B_k=\{P_{x,x^3+x}:x\in\mathrm{GF}(2^k)\}$ in Theorem 15.6.
--
--   **Formalization Note** The coordinate map is `b.repr`.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Theorem 15.6, p.291, and Step 1 of its proof, p.292 (PDF pp.291-292)

import Mathlib
import Definitions.Def_SpencerEight_Supplement_pauliP

namespace SpencerEight.Supplement

/-- The member `P_x := P_{x, x³+x}` of the family `B_k` of Theorem 15.6 (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.291
(PDF p.291)), for `x ∈ GF(2^k)`, where `F₂^k` is identified with `GF(2^k)` through the basis `b`:
`x = ∑ᵢ cᵢ bᵢ ↔ c = (c₁, …, c_k)`. So `P_x = P_{φ(x), φ(x³+x)}` with `φ` the coordinate map of `b`;
`x³ + x` is computed in `GF(2^k)` and then read as a vector.

**Formalization Note** `GF(2^k)` is `GaloisField 2 k`; the coordinate map is `b.repr`. The theorem
applies this to a self-dual basis (`IsSelfDualBasis b`), for which `φ(x)ᵢ = Tr[x bᵢ]`. -/
noncomputable def familyB {k : ℕ} (b : Module.Basis (Fin k) (ZMod 2) (GaloisField 2 k))
    (x : GaloisField 2 k) : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℝ :=
  pauliP (fun i => b.repr x i) (fun i => b.repr (x ^ 3 + x) i)

end SpencerEight.Supplement


