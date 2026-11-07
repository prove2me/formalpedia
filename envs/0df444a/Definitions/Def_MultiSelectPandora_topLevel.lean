-- Prove2me | Definitions.Def_MultiSelectPandora_topLevel
-- name    : MultiSelectPandora_topLevel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:18:34.163003+00:00
-- url     : https://prove2.me/theorems/43fdef11-22cd-4388-996b-41f823aea937
-- title:
--   The level $\top$
-- statement:
--   The additional level $\top$ of the discretization, as a real number:
--   $$\top=\max\{\mathrm{MaxV},\ \text{the largest value of the instance}\}+1.$$
--   It lies above every grid point, and $\varphi(\top)=0$.
--
--   **Formalization Note** Footnote 2 reads $\top$ as "an arbitrary fixed number greater than MaxV; nothing depends on the choice". Remark A.4 and Claim A.7 need $D^L(v)\ge v$ for every $v$, and $g\le0$ at the floor $\top$, which holds only if $\top$ is at least every value. With $\top=\mathrm{MaxV}+1$, Claim 3.30 fails. Take two boxes, each with value $1000$ with probability $0.1$ and $0$ otherwise, $c=90$, $k=1$, $\varepsilon=1/4$. Then $\theta=476$ and $\top=477$, and the policy opening both boxes has expected total reward larger on $I^{SL}$ than on $I$ by $5.23$. This definition therefore takes $\top$ above every value, which is one of the numbers the footnote allows.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Definition 3.21 with footnote 2, p.15 (PDF p.16); Remark A.4, p.31 (PDF p.32); Claim A.7, pp.35–36 (PDF pp.36–37)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_MaxV

namespace MultiSelectPandora

/-- **The level `⊤`, as a real number.** Beyhaghi–Han–Luqman manuscript, Definition 3.21 with footnote 2, p.15 (PDF p.16), and
Remark A.4, p.31 (PDF p.32).

**Formalization Note.** Here `⊤ = max{MaxV, largest value of the instance} + 1`. Footnote 2 reads `⊤` as "an arbitrary fixed
number greater than `MaxV`; nothing depends on the choice", but Remark A.4 needs "`D^L(v) ≥ v` … for every `v`" and "every action
has `g ≤ 0`" when `⊤` is the floor, and Claim A.7 needs the same. These hold only if `⊤` is at least every value. With
`⊤ = MaxV + 1`, Claim 3.30 fails: two boxes, each `1000` with probability `0.1` and else `0`, `c = 90`, `k = 1`, `ε = 1/4`, give
`θ = 476` and `⊤ = 477`, and opening both boxes has reward larger on `I^SL` than on `I` by `5.23`. -/
noncomputable def topLevel (I : Inst) (k : ℕ) (ε : ℝ) : ℝ :=
  Finset.univ.fold max (MaxV I k ε) (fun i => Finset.univ.fold max 0 (I.val i)) + 1

end MultiSelectPandora


