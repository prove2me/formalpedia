-- Prove2me | Definitions.Def_NarrowDNF_CertificateBounds
-- name    : NarrowDNF_CertificateBounds
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T07:59:59.272855+00:00
-- url     : https://prove2.me/theorems/22c91e26-626d-4232-84f9-7f14db55e296
-- title:
--   Boolean evaluation of the certificate-truncated positive DNF
-- statement:
--   Let $I$ be finite, $J$ a local activation family, $u:\{0,1\}^I\to\{0,1\}$ a Boolean readout, and $w\in\mathbb N$ a certificate-size cutoff. For an input $z$, let $T_J(z)$ be the coordinates that are both active under $J$ and labelled one in $z$. Retain exactly the terms $T_J(z)$ arising from accepted inputs $u(z)=1$ with $|T_J(z)|\le w$.
--
--   The function defined by this bundle is the actual finite disjunction
--   $$g_w(x)=\mathbf1\!\left[\exists z:\ u(z)=1,\ |T_J(z)|\le w,\ \forall i\in T_J(z),\ x_i=1\right].$$
--   It is implemented by Boolean evaluation of the already defined finite set of truncated certificate terms, with duplicate terms removed. The empty disjunction evaluates to false and an empty term evaluates to true. No monotonicity, measurability, positive-certificate property, or approximation error estimate is assumed by the definition; those hypotheses and conclusions belong to the certificate-bound theorem nodes.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/CertificateBounds.lean#L9-L11

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_Certificates

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation


namespace NarrowDNF
namespace Activation
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def truncatedDNF (J : Activation ι) (u : Cube ι → Bool)
    (w : ℕ) (x : Cube ι) : Bool := by
  classical exact decide (DNFHolds (J.truncatedTerms u w) x)











end Activation
end NarrowDNF


