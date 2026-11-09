-- Prove2me | Definitions.Def_IsRandomnessNecessaryADA_Plain_ConditionalCube
-- name    : IsRandomnessNecessaryADA_Plain_ConditionalCube
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:16:02.473015+00:00
-- url     : https://prove2.me/theorems/f4c0fe33-5f50-4e96-ae39-87b704d4c8fd
-- title:
--   Fair-coordinate conditional laws and the discrete-TV adapter
-- statement:
--   A Boolean cube is the sign cube under $0\leftrightarrow-1$ and $1\leftrightarrow+1$. For a uniform cube point, overwriting coordinate $u$ with $b$ has exactly the conditional law given $X_u=b$, since this event has probability $1/2$. Every other coordinate remains independent and fair.
--
--   The probability-mass-function adapter uses the published general discrete total variation definition:
--   $$\operatorname{TV}(p,q)=\tfrac12\sum_z|p(z)-q(z)|.$$
--   It passes the real masses of the two PMFs to that definition. All uses here have finite output cubes, hence convergent sums. The general discrete-law and coupling predicates remain the imported published objects rather than local replacements. This bundle supplies the conditional distributions used in Lemma 1.5 without conditioning on a zero-probability event.
-- source:
--   Edith Cohen, Haim Kaplan, Yishay Mansour, Shay Sapir, Uri Stemmer, Eliad Tsfadia, STOC 2027 submission #267 (October 2026), Lemma 1.5 and the discrete-TV convention, p.5; §4.1, pp.9–10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/267.pdf; PDF/printed pages coincide.

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P44
import Definitions.Def_IsRandomnessNecessaryADA_Plain_Protocol

set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain

/-- Bool encodes the signs by false ↔ −1 and true ↔ +1.
Overwriting a coordinate of a uniform cube is its conditional law at that fair bit. -/
noncomputable def coordinateLaw {M : ℕ} (u : Fin M) (b : Bool) :
    PMF (Fin M → Bool) :=
  (PMF.uniformOfFintype (Fin M → Bool)).map (fun x => Function.update x u b)

/-- Adapter only: the imported arbitrary-discrete half-L1 definition on PMF masses. -/
noncomputable def pmfTV {Z : Type} (p q : PMF Z) : ℝ :=
  QAlgorithms.Papers.Independent.Bridge50.P44.discreteTV
    (fun z => (p z).toReal) (fun z => (q z).toReal)

end IsRandomnessNecessaryADA.Plain


