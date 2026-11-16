-- Prove2me | Definitions.Def_CompDesign_Supplement_shapleyPay
-- name    : CompDesign_Supplement_shapleyPay
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:49:27.860789+00:00
-- url     : https://prove2.me/theorems/b391d458-d0ef-4c50-b442-2bf38c8376a3
-- title:
--   Shapley payment rule $p^{Sh}$ (7)
-- statement:
--   For a value function $v$ and budget $B$, the **Shapley payment rule** is
--   $$p^{Sh}_i(S)=\begin{cases}B\,\varphi_i(S)/v(S)&\text{if }i\in S\text{ and }v(S)>0,\\0&\text{otherwise,}\end{cases}$$
--   where $\varphi_i(S)=\sum_{T\subseteq S\setminus\{i\}}\frac{|T|!\,(|S|-|T|-1)!}{|S|!}\,(v(T\cup\{i\})-v(T))$ is the Shapley value (6) of $i$ in $v$ restricted to $S$. It is the rule of Theorem 4.2.
--
--   **Formalization Note** $\varphi_i(S)$ is the published `MondererShapley.Participation.shapleyOn S v i`, which is (6) verbatim.
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), (6)–(7), p.15 (PDF 18)

import Mathlib
import Definitions.Def_MondererShapley_Participation_shapleyOn

namespace CompDesign.Supplement

/-- The Shapley payment rule (7) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…), §3.2.1, p.15 (PDF 18):
`p^Sh_i(S) = B φ_i(S)/v(S)` if `i ∈ S` and `v(S) > 0`, and `0` otherwise, where `φ_i(S)` is the
Shapley value (6) of `i` in `v` restricted to `S`.

**Formalization Note.** `φ_i(S)` is the published `MondererShapley.Participation.shapleyOn S v i`,
which is (6) verbatim (weights `|T|!(|S|−|T|−1)!/|S|!` over `T ⊆ S ∖ {i}`). -/
noncomputable def shapleyPay {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (S : Finset (Fin n))
    (i : Fin n) : ℝ :=
  if i ∈ S ∧ 0 < v S then B * MondererShapley.Participation.shapleyOn S v i / v S else 0

end CompDesign.Supplement


