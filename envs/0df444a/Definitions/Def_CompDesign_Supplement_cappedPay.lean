-- Prove2me | Definitions.Def_CompDesign_Supplement_cappedPay
-- name    : CompDesign_Supplement_cappedPay
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:52:12.01418+00:00
-- url     : https://prove2.me/theorems/a0237821-3410-4f7d-9e92-284c641573ed
-- title:
--   Branches of the multi-agent randomized rule of §7.2: singleton prize, capped marginal potential, scales
-- statement:
--   In the multi-agent combinatorial model:
--
--   1. **Singleton-prize branch.** For a fixed $e^*\in\arg\max_e v(\{e\})$ with owner $i(e^*)$: $p^{sing}_i(S)=B$ if $i=i(e^*)$ and $e^*\in S_i$, else $0$.
--   2. **Capped branch with scale $R$.** With $F_R(S)=B\min\{v(S)/R,1\}$, $p^R_i(S)=F_R(S)-F_R(S_{-i})$, where $S_{-i}=S\setminus A_i$.
--   3. **Scales.** $R_r=v(A)/(3/2)^r$ (56), $r=0,\dots,L$, with $L=\lceil\log_{3/2}(4q/3)\rceil$ (55) and $q$ of (54).
--
--   The randomized rule of Theorem 7.5 draws uniformly one of the $L+2$ branches.
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), §7.2.1–7.2.2, pp.58–61 (PDF 61–64), (54)–(56)

import Mathlib
import Definitions.Def_CompDesign_Supplement_blockCount

namespace CompDesign.Supplement

/-- The singleton-prize branch of §7.2.1, p.58 (PDF 61), of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…): for a fixed
`e* ∈ argmax_e v({e})` with owner `own e*`, `p^sing_i(S) = B` if `i = own e*` and `e* ∈ S_i`,
and `0` otherwise. -/
def combSingletonPay {n m : ℕ} (B : ℝ) (own : Fin m → Fin n) (estar : Fin m)
    (S : Finset (Fin m)) (i : Fin n) : ℝ :=
  if own estar = i ∧ estar ∈ S then B else 0

/-- The capped payment potential `F_R(S) = B min{v(S)/R, 1}` of §7.2.1, p.58 (PDF 61), of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…). -/
noncomputable def cappedF {m : ℕ} (v : Finset (Fin m) → ℝ) (B R : ℝ) (S : Finset (Fin m)) : ℝ :=
  B * min (v S / R) 1

/-- The capped marginal-potential branch with scale `R` (§7.2.1, p.58, PDF 61, of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…)):
`p^R_i(S) = F_R(S) − F_R(S_{−i})`, where `S_{−i} = S ∖ A_i` is the union of the other agents'
choices. -/
noncomputable def cappedPay {n m : ℕ} (v : Finset (Fin m) → ℝ) (B R : ℝ) (own : Fin m → Fin n)
    (S : Finset (Fin m)) (i : Fin n) : ℝ :=
  cappedF v B R S - cappedF v B R (S.filter (fun e => own e ≠ i))

/-- The scales (56) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…), p.61 (PDF 64): `R_r = v(A)/(3/2)^r`. -/
noncomputable def scale {m : ℕ} (v : Finset (Fin m) → ℝ) (r : ℕ) : ℝ :=
  v Finset.univ / (3 / 2 : ℝ) ^ r

/-- The number `L = ⌈log_{3/2}(4q/3)⌉` of (55), p.61 (PDF 64), of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…), with `q` of (54). The
randomized rule mixes uniformly over the `L + 2` branches (singleton prize, `R_0, …, R_L`).

**Formalization Note.** For `m = 0` the argument of the logarithm is `0` and `L = 0`; every statement
is trivial there. -/
noncomputable def numScales (m : ℕ) (l : ℝ) : ℕ :=
  ⌈Real.logb (3 / 2) (4 * (blockCount m l : ℝ) / 3)⌉₊

end CompDesign.Supplement


