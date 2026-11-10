-- Prove2me | Definitions.Def_OptGaussTomo_IsValidCov
-- name    : OptGaussTomo_IsValidCov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:06:24.4886+00:00
-- url     : https://prove2.me/theorems/b085f407-0af0-4162-aea8-f283d5c5b121
-- title:
--   Valid bosonic covariance matrices
-- statement:
--   A real $2m\times2m$ matrix $V$ (interleaved quadratures, vacuum $=I$) is a **valid covariance matrix** if it is the covariance matrix of some $m$-mode Gaussian state; the mean can be taken to be $0$. Equivalently, $V=V^{\mathsf T}$ and $V+i\Omega\succeq0$.
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), Lemma D.13 p.55 (pdf p.55); Lemma D.14 p.56; Theorem D.15 p.58

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14 (OscillatorCovariance GaussianAt)

namespace OptGaussTomo

/-!
# Valid bosonic covariance matrices

Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, *Optimal tomography of bosonic and
fermionic Gaussian states*, arXiv:2607.11847 (held version, sha256 0f7548a2…), Lemma D.13, p.55:
"Let `W` be a valid `2m × 2m` bosonic covariance matrix"; Lemma D.14, p.56 and Theorem D.15, p.58
("outputs a Gaussian state `ρ̂ = ρ_{μ̂,V̂}`").

**Formalization Note.** A real `2m × 2m` matrix (interleaved quadratures, vacuum `= I`) is a
valid covariance matrix iff it is the covariance of some `m`-mode Gaussian state; the mean can be
taken to be `0` (displacements change only the mean). Equivalently `V = Vᵀ` and `V + iΩ ⪰ 0`.
-/

/-- `V` is the covariance matrix of some Gaussian state on the modes `I`. -/
def IsValidCov {I : Type} [Fintype I] (V : OscillatorCovariance I) : Prop :=
  ∃ ρ : State (Occupation I), GaussianAt ρ.coefficients 0 V

end OptGaussTomo


