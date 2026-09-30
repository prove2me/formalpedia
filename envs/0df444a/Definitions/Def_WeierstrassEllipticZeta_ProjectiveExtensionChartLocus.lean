-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionChartLocus
-- name    : WeierstrassEllipticZeta_ProjectiveExtensionChartLocus
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-08T17:11:15.67972+00:00
-- url     : https://prove2.me/theorems/304d079e-9b18-4de4-9a38-8d704a7c9cba
-- title:
--   The two-chart part of the elliptic-extension projective locus
-- statement:
--   For complex $g_2,g_3$, let $Z_{g_2,g_3}$ be the projective locus defined by
--
--   $$X_0X_4-X_2X_3-2X_1^2=0,\qquad
--   X_0X_2^2-4X_1^3+g_2X_0^2X_1+g_3X_0^3=0.$$
--
--   Define its two-chart part
--
--   $$Z^\circ_{g_2,g_3}=\{[X]\in Z_{g_2,g_3}:X_0\ne0\ \text{or}\ X_2\ne0\}.$$
--
--   The formal type is the subtype whose standard chosen representative satisfies this nonvanishing alternative. Containment of the elliptic-extension image is a separate theorem obligation. The definition assumes no group structure, dimension or smoothness.
-- source:
--   Derived from the regular and lattice-point descriptions of the exponential map in Senthil Kumar K (2026), Appendix A.2 between (A.3) and (A.4), https://doi.org/10.1017/S001309152610145X. The regular display normalizes projective coordinate zero, and the lattice display normalizes projective coordinate two.

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionLocus

noncomputable section
namespace WeierstrassEllipticZeta

/-- The part of the quadratic-cubic projective locus covered by the charts X₀ ≠ 0
and X₂ ≠ 0. The condition is imposed on the standard chosen representative.
Containment of the elliptic-extension image is a separate theorem obligation.
No group structure, dimension or smoothness is assumed. -/
def ProjectiveExtensionChartLocus (g₂ g₃ : ℂ) :=
  {p : ProjectiveExtensionLocus g₂ g₃ // p.val.rep 0 ≠ 0 ∨ p.val.rep 2 ≠ 0}

end WeierstrassEllipticZeta


