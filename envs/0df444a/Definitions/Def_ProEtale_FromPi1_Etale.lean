-- Prove2me | Definitions.Def_ProEtale_FromPi1_Etale
-- name    : ProEtale_FromPi1_Etale
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:56:36.978503+00:00
-- url     : https://prove2.me/theorems/4d1b90d0-e0ab-41b7-abc9-eeb0eb8d992b
-- title:
--   Étale morphisms of schemes are flat
-- statement:
--   For a morphism of schemes $f\colon X \to Y$:
--   $$f \text{ étale} \;\Longrightarrow\; f \text{ flat}.$$
--   The file records this as an instance, so that flatness of étale morphisms is found automatically.
--
--   **Formalization Note** The declaration is the anonymous instance `AlgebraicGeometry.inst_FromPi1Etale_L12 : Flat f` for `[Etale f]`. It is proved by `inferInstance`, i.e. Mathlib already provides it. A source comment says it comes from a $\pi_1$ formalization project and is being upstreamed to Mathlib.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/FromPi1/Etale.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.RingHom.Smooth

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
universe u

open CategoryTheory

namespace AlgebraicGeometry

-- This exists in Pi1 and is being upstreamed to mathlib.
instance inst_FromPi1Etale_L12 {X Y : Scheme} (f : X ⟶ Y) [Etale f] : Flat f :=
  inferInstance

end AlgebraicGeometry


