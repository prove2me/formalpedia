-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_tiltPoiss
-- name    : TwoFoldOPI_Supplement_tiltPoiss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:49:29.156367+00:00
-- url     : https://prove2.me/theorems/8c948d19-1318-41d7-b5da-9a25e567d82e
-- title:
--   The tilted Poisson distribution $\mathrm{TiltPoiss}_{\nu,B}$
-- statement:
--   Fix $\nu>0$ and a nonempty set $B\subseteq\mathbb Z_{\ge0}$. The **tilted Poisson distribution** $\mathrm{TiltPoiss}_{\nu,B}$ is the distribution on $\mathbb Z_{\ge 0}$ with
--   $$p_k=\frac{1}{Z(\nu,B)}\,\mathbf 1[k\in B]\,\frac{\nu^k}{k!},\qquad Z(\nu,B)=\sum_{k\in B}\frac{\nu^k}{k!}.$$
--
--   It is the limiting law of the load of one symbol of class $r$ in a uniform word of a special-form load set, and it enters the stay probability $p_{\mathrm{stay}}$ of Theorems 10.11, 11.3, 11.9 and 12.2.
--
--   **Formalization Note** $B$ is a set of natural numbers. For $\nu>0$ and $B\ne\emptyset$ (assumed by every statement using it) the series converges and $Z(\nu,B)>0$.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.4, Definition 5.35, eqs. (9)–(10), p. 33

import Mathlib

namespace TwoFoldOPI

namespace Supplement

/-- **The tilted Poisson distribution `TiltPoiss_{ν,B}`.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.4, Definition 5.35, p.33: "Fix a parameter ν > 0 and a nonempty subset B ⊆ Z_{≥0}.
Define the tilted Poisson distribution TiltPoiss_{ν,B} to be the distribution on Z_{≥0} with
probabilities: p_k := (1/Z(ν, B)) 1[k ∈ B] ν^k/k!, (9) where we define the partition function:
Z(ν, B) := Σ_{k∈B} ν^k/k!, (10)".

`tiltZ ν B = Σ_{k ∈ B} ν^k/k!` and `tiltPoiss ν B k = 1[k ∈ B] (ν^k/k!) / Z(ν, B)`.

**Formalization Note.** `B` is a set of natural numbers (`ℤ_{≥0} = ℕ`). For `ν > 0` and
`B ≠ ∅` (the paper's hypotheses, required by every statement using it) the series converges and
`Z(ν, B) > 0`, so `tiltPoiss ν B` is a probability mass function on `ℕ`. -/
noncomputable def tiltZ (ν : ℝ) (B : Set ℕ) : ℝ :=
  ∑' k : ℕ, B.indicator (fun j : ℕ => ν ^ j / (j.factorial : ℝ)) k

/-- The probability `p_k` of `k` under `TiltPoiss_{ν,B}` (Definition 5.35, eq. (9), p.33). -/
noncomputable def tiltPoiss (ν : ℝ) (B : Set ℕ) (k : ℕ) : ℝ :=
  B.indicator (fun j : ℕ => ν ^ j / (j.factorial : ℝ)) k / tiltZ ν B

end Supplement

end TwoFoldOPI


