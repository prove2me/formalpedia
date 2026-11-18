-- Prove2me | Definitions.Def_NearLogSetCover966_SeparatorComposition
-- name    : NearLogSetCover966_SeparatorComposition
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-17T23:57:15.95229+00:00
-- url     : https://prove2.me/theorems/c8cafaf1-81ad-4c28-80ee-f828ab5cc817
-- title:
--   Composition of finite binary linear separator families
-- statement:
--   Let $H_1$ be a finite family of binary linear maps from $\mathbb F_2^D$ to $\mathbb F_2^{d_1}$, and let $H_2$ be such a family from $\mathbb F_2^{d_1}$ to $\mathbb F_2^{d_2}$. Their composition family is
--
--   $$H_2\circ H_1=\{B A:A\in H_1,\ B\in H_2\}.$$
--
--   The stored list contains every such matrix product, with duplicates removed. This is the construction used in Lemma A.3 to combine two linear separators.
-- source:
--   Bingkai Lin and Xin Zheng, Near-Logarithmic Inapproximability of Parameterized Set Cover, STOC 2027 submission #966, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/966.pdf, Appendix A, Lemma A.3 and its proof, printed p.30 (PDF p.32).

import Definitions.Def_NearLogSetCover966_Main_Core
set_option autoImplicit false
namespace NearLogSetCover966.Main

def HashFamily.compose {D d₁ d₂ : ℕ}
    (H₁ : HashFamily D d₁) (H₂ : HashFamily d₁ d₂) : HashFamily D d₂ where
  maps := (H₁.maps.flatMap fun a => H₂.maps.map fun b => b * a).dedup
  nodup := List.nodup_dedup _

end NearLogSetCover966.Main


