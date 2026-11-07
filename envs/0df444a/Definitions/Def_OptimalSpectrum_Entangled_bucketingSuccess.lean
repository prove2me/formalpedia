-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_bucketingSuccess
-- name    : OptimalSpectrum_Entangled_bucketingSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:19:32.216871+00:00
-- url     : https://prove2.me/theorems/fc7f83f3-7707-4c8a-9ac2-69b4ea729f31
-- title:
--   Success of a bucketing outcome: bounds (i)–(iii) of Definition 5.1
-- statement:
--   Fix $0<B<1$, $0<\eta<1$ and a density matrix $\rho$ on $\mathbb C^d$. For a bucketing outcome $(\Pi,\widehat\alpha_{\mathrm{Large}})$ put
--
--   $$\sigma=\overline\Pi\rho\overline\Pi,\qquad \alpha_{\mathrm{Large}}=\mathrm{spec}\big(\Pi\rho\Pi|_{\mathrm{ran}\,\Pi}\big).$$
--
--   The outcome is **successful** at $(B,\eta)$ when all three bounds hold:
--
--   1. (i) $d_{\mathrm{TV}}(\alpha_{\mathrm{Large}},\widehat\alpha_{\mathrm{Large}})\le\eta$;
--   2. (ii) $0\preceq\sigma\preceq1.1B\,I_d$;
--   3. (iii) $d_{\mathrm{TV}}\big(\mathrm{spec}(\rho),\mathrm{spec}(\Pi\rho\Pi+\sigma)\big)\le\eta$.
--
--   Here $d_{\mathrm{TV}}(p,q)=\tfrac12\|p-q\|_1$. The second stage of the paper's algorithm estimates the spectrum of the small-bucket state $\sigma$.
--
--   **Formalization Note** $\alpha_{\mathrm{Large}}$ is encoded as the full sorted spectrum of $\Pi\rho\Pi$ and compared with the zero-padded $\widehat\alpha_{\mathrm{Large}}$; the eigenvalues of $\Pi\rho\Pi$ beyond the first $\mathrm{rank}\,\Pi$ vanish, so the distance is the same. $d_{\mathrm{TV}}$ is the platform's `Support50.P38.tv`.
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, Definition 5.1, p. 12 (PDF p. 14)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38
import Definitions.Def_OptimalSpectrum_Entangled_spec
import Definitions.Def_OptimalSpectrum_Entangled_BucketOutcome

open scoped Matrix ComplexOrder

namespace OptimalSpectrum.Entangled

/-- **The three success bounds (i)–(iii) of a bucketing outcome.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, Definition 5.1, printed p. 12 (PDF p. 14). For an outcome `(Π, α̂_Large)`, put `Π̄ = I − Π`,
`σ = Π̄ρΠ̄` and `α_Large = spec(ΠρΠ|_ran Π)`. The outcome is *successful* at `(B, η)` when

1. (i) `d_TV(α_Large, α̂_Large) ≤ η`;
2. (ii) `0 ⪯ σ ⪯ 1.1 B I_d`;
3. (iii) `d_TV(spec(ρ), spec(ΠρΠ + σ)) ≤ η`.

**Formalization Note.** `d_TV(p,q) = ½‖p − q‖₁` is the platform's `Support50.P38.tv`. In (i),
`α_Large` is encoded as the full sorted spectrum `spec(ΠρΠ)` of length `d` and `α̂_Large` as its
zero-padding (see `BucketOutcome`): the eigenvalues of `ΠρΠ` beyond the first `rank Π` are zero,
so both padded vectors agree with the length-`rank Π` lists followed by zeros and the distance is the
same. `1.1` is written `11/10`. -/
noncomputable def bucketingSuccess {d : ℕ} (B η : ℝ) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (o : BucketOutcome d) : Prop :=
  let P : Matrix (Fin d) (Fin d) ℂ := Matrix.of o.1.1
  let σ : Matrix (Fin d) (Fin d) ℂ := (1 - P) * ρ * (1 - P)
  QAlgorithms.Papers.Independent.Support50.P38.tv (spec (P * ρ * P)) o.1.2 ≤ η ∧
  σ.PosSemidef ∧ ((((11 / 10 : ℝ) * B : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - σ).PosSemidef ∧
  QAlgorithms.Papers.Independent.Support50.P38.tv (spec ρ) (spec (P * ρ * P + σ)) ≤ η

end OptimalSpectrum.Entangled


