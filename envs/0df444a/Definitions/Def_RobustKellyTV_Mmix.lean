-- Prove2me | Definitions.Def_RobustKellyTV_Mmix
-- name    : RobustKellyTV_Mmix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:35:46.952914+00:00
-- url     : https://prove2.me/theorems/38b2852a-5295-4147-8ebb-4fa78bcc64b9
-- title:
--   The mixed e-process $M^{\mathrm{mix}}=\tfrac12M^{\mathrm{CK}}+\tfrac12M^{\mathrm F}$
-- statement:
--   The **mixed e-process** is
--
--   $$M^{\mathrm{mix}}_n=\tfrac12M^{\mathrm{CK}}_n+\tfrac12M^{\mathrm F}_n,$$
--
--   where $M^{\mathrm{CK}}$ is the clipped-Kelly process with the Laplace pseudocounts $\alpha_1=\dots=\alpha_d=1$ and $M^{\mathrm F}$ is the learn-an-event process. It retains the guarantees of both components.
-- source:
--   A. Saha, A. Ramdas, Beyond least-favorable distribution pairs: asymptotically instance-optimal robust hypothesis testing, arXiv:2611.02130v1, §3.3 eq. (30) p.12

import Mathlib
import Definitions.Def_RobustKellyTV_MF

namespace RobustKellyTV

variable {d : ℕ}

/-- The mixed e-process `M^mix_n = ½ M^CK_n + ½ M^F_n` (arXiv:2611.02130v1, eq. (30), p.12), where
`M^CK` is the clipped-Kelly process with the Laplace pseudocounts (16). It takes no level `α`. -/
noncomputable def Mmix (σ : Setting d) (n : ℕ) (x : ℕ → Fin d) : ℝ :=
  (1 / 2) * Mck σ (laplace d) n x + (1 / 2) * MF σ n x

end RobustKellyTV


