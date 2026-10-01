-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b00_q01
-- name    : CK_CKLaneC2R_EndpointCover_b00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T09:28:42.805979+00:00
-- url     : https://prove2.me/theorems/35a626f0-b4d8-4b22-bad6-0b4c6cc4f2c7
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 2 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 2 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 2 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 2 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 1 of 5) (piece 2 of 5).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B027
import Definitions.Def_CK_CKLaneC2R_EpCells_B028
import Definitions.Def_CK_CKLaneC2R_EpCells_B029
namespace CKLaneC2R.EndpointCover
theorem cover_sub_001 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : a ≤ ((3249/16000 : ℚ) : ℝ)) (h4 : a ≤ ((5649/32000 : ℚ) : ℝ)) (h5 : a ≤ ((10449/64000 : ℚ) : ℝ)) (h6 : a ≤ ((20049/128000 : ℚ) : ℝ)) (h7 : a ≤ ((39249/256000 : ℚ) : ℝ)) (h8 : ¬ (a ≤ ((77649/512000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h136 : a ≤ ((156147/1024000 : ℚ) : ℝ)
  · -- left
    by_cases h137 : a ≤ ((62289/409600 : ℚ) : ℝ)
    · -- left
      by_cases h138 : a ≤ ((622041/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h139 : a ≤ ((1243233/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h140 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h141 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h142 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B027.e1656_pos (not_le.mp h8).le h139 hz1 h142 hz
              · -- right
                exact CKLaneC2R.EpCells.B027.e1658_pos (not_le.mp h8).le h139 (not_le.mp h142).le h141 hz
            · -- right
              by_cases h143 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B027.e1664_pos (not_le.mp h8).le h139 (not_le.mp h141).le h143 hz
              · -- right
                exact CKLaneC2R.EpCells.B027.e1666_pos (not_le.mp h8).le h139 (not_le.mp h143).le h140 hz
          · -- right
            by_cases h144 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h145 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1688_pos (not_le.mp h8).le h139 (not_le.mp h140).le h145 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1690_pos (not_le.mp h8).le h139 (not_le.mp h145).le h144 hz
            · -- right
              by_cases h146 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1696_pos (not_le.mp h8).le h139 (not_le.mp h144).le h146 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1698_pos (not_le.mp h8).le h139 (not_le.mp h146).le hz2 hz
        · -- right
          by_cases h147 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h148 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h149 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B027.e1657_pos (not_le.mp h139).le h138 hz1 h149 hz
              · -- right
                exact CKLaneC2R.EpCells.B027.e1659_pos (not_le.mp h139).le h138 (not_le.mp h149).le h148 hz
            · -- right
              by_cases h150 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B027.e1665_pos (not_le.mp h139).le h138 (not_le.mp h148).le h150 hz
              · -- right
                exact CKLaneC2R.EpCells.B027.e1667_pos (not_le.mp h139).le h138 (not_le.mp h150).le h147 hz
          · -- right
            by_cases h151 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h152 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1689_pos (not_le.mp h139).le h138 (not_le.mp h147).le h152 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1691_pos (not_le.mp h139).le h138 (not_le.mp h152).le h151 hz
            · -- right
              by_cases h153 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1697_pos (not_le.mp h139).le h138 (not_le.mp h151).le h153 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1699_pos (not_le.mp h139).le h138 (not_le.mp h153).le hz2 hz
      · -- right
        by_cases h154 : a ≤ ((1244931/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h155 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h156 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h157 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B027.e1660_pos (not_le.mp h138).le h154 hz1 h157 hz
              · -- right
                exact CKLaneC2R.EpCells.B027.e1662_pos (not_le.mp h138).le h154 (not_le.mp h157).le h156 hz
            · -- right
              by_cases h158 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B027.e1668_pos (not_le.mp h138).le h154 (not_le.mp h156).le h158 hz
              · -- right
                exact CKLaneC2R.EpCells.B027.e1670_pos (not_le.mp h138).le h154 (not_le.mp h158).le h155 hz
          · -- right
            by_cases h159 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h160 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1692_pos (not_le.mp h138).le h154 (not_le.mp h155).le h160 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1694_pos (not_le.mp h138).le h154 (not_le.mp h160).le h159 hz
            · -- right
              by_cases h161 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1700_pos (not_le.mp h138).le h154 (not_le.mp h159).le h161 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1702_pos (not_le.mp h138).le h154 (not_le.mp h161).le hz2 hz
        · -- right
          by_cases h162 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h163 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h164 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B027.e1661_pos (not_le.mp h154).le h137 hz1 h164 hz
              · -- right
                exact CKLaneC2R.EpCells.B027.e1663_pos (not_le.mp h154).le h137 (not_le.mp h164).le h163 hz
            · -- right
              by_cases h165 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B027.e1669_pos (not_le.mp h154).le h137 (not_le.mp h163).le h165 hz
              · -- right
                exact CKLaneC2R.EpCells.B027.e1671_pos (not_le.mp h154).le h137 (not_le.mp h165).le h162 hz
          · -- right
            by_cases h166 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h167 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1693_pos (not_le.mp h154).le h137 (not_le.mp h162).le h167 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1695_pos (not_le.mp h154).le h137 (not_le.mp h167).le h166 hz
            · -- right
              by_cases h168 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1701_pos (not_le.mp h154).le h137 (not_le.mp h166).le h168 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1703_pos (not_le.mp h154).le h137 (not_le.mp h168).le hz2 hz
    · -- right
      by_cases h169 : a ≤ ((623739/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h170 : a ≤ ((1246629/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h171 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h172 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h173 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B027.e1672_pos (not_le.mp h137).le h170 hz1 h173 hz
              · -- right
                exact CKLaneC2R.EpCells.B027.e1674_pos (not_le.mp h137).le h170 (not_le.mp h173).le h172 hz
            · -- right
              by_cases h174 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1680_pos (not_le.mp h137).le h170 (not_le.mp h172).le h174 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1682_pos (not_le.mp h137).le h170 (not_le.mp h174).le h171 hz
          · -- right
            by_cases h175 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h176 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1704_pos (not_le.mp h137).le h170 (not_le.mp h171).le h176 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1706_pos (not_le.mp h137).le h170 (not_le.mp h176).le h175 hz
            · -- right
              by_cases h177 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1712_pos (not_le.mp h137).le h170 (not_le.mp h175).le h177 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1714_pos (not_le.mp h137).le h170 (not_le.mp h177).le hz2 hz
        · -- right
          by_cases h178 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h179 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h180 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B027.e1673_pos (not_le.mp h170).le h169 hz1 h180 hz
              · -- right
                exact CKLaneC2R.EpCells.B027.e1675_pos (not_le.mp h170).le h169 (not_le.mp h180).le h179 hz
            · -- right
              by_cases h181 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1681_pos (not_le.mp h170).le h169 (not_le.mp h179).le h181 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1683_pos (not_le.mp h170).le h169 (not_le.mp h181).le h178 hz
          · -- right
            by_cases h182 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h183 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1705_pos (not_le.mp h170).le h169 (not_le.mp h178).le h183 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1707_pos (not_le.mp h170).le h169 (not_le.mp h183).le h182 hz
            · -- right
              by_cases h184 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1713_pos (not_le.mp h170).le h169 (not_le.mp h182).le h184 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1715_pos (not_le.mp h170).le h169 (not_le.mp h184).le hz2 hz
      · -- right
        by_cases h185 : a ≤ ((1248327/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h186 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h187 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h188 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B027.e1676_pos (not_le.mp h169).le h185 hz1 h188 hz
              · -- right
                exact CKLaneC2R.EpCells.B027.e1678_pos (not_le.mp h169).le h185 (not_le.mp h188).le h187 hz
            · -- right
              by_cases h189 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1684_pos (not_le.mp h169).le h185 (not_le.mp h187).le h189 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1686_pos (not_le.mp h169).le h185 (not_le.mp h189).le h186 hz
          · -- right
            by_cases h190 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h191 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1708_pos (not_le.mp h169).le h185 (not_le.mp h186).le h191 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1710_pos (not_le.mp h169).le h185 (not_le.mp h191).le h190 hz
            · -- right
              by_cases h192 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1716_pos (not_le.mp h169).le h185 (not_le.mp h190).le h192 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1718_pos (not_le.mp h169).le h185 (not_le.mp h192).le hz2 hz
        · -- right
          by_cases h193 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h194 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h195 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B027.e1677_pos (not_le.mp h185).le h136 hz1 h195 hz
              · -- right
                exact CKLaneC2R.EpCells.B027.e1679_pos (not_le.mp h185).le h136 (not_le.mp h195).le h194 hz
            · -- right
              by_cases h196 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1685_pos (not_le.mp h185).le h136 (not_le.mp h194).le h196 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1687_pos (not_le.mp h185).le h136 (not_le.mp h196).le h193 hz
          · -- right
            by_cases h197 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h198 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1709_pos (not_le.mp h185).le h136 (not_le.mp h193).le h198 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1711_pos (not_le.mp h185).le h136 (not_le.mp h198).le h197 hz
            · -- right
              by_cases h199 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1717_pos (not_le.mp h185).le h136 (not_le.mp h197).le h199 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1719_pos (not_le.mp h185).le h136 (not_le.mp h199).le hz2 hz
  · -- right
    by_cases h200 : a ≤ ((313143/2048000 : ℚ) : ℝ)
    · -- left
      by_cases h201 : a ≤ ((625437/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h202 : a ≤ ((50001/327680 : ℚ) : ℝ)
        · -- left
          by_cases h203 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h204 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h205 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1720_pos (not_le.mp h136).le h202 hz1 h205 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1722_pos (not_le.mp h136).le h202 (not_le.mp h205).le h204 hz
            · -- right
              by_cases h206 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1728_pos (not_le.mp h136).le h202 (not_le.mp h204).le h206 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1730_pos (not_le.mp h136).le h202 (not_le.mp h206).le h203 hz
          · -- right
            by_cases h207 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h208 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1752_pos (not_le.mp h136).le h202 (not_le.mp h203).le h208 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1754_pos (not_le.mp h136).le h202 (not_le.mp h208).le h207 hz
            · -- right
              by_cases h209 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1760_pos (not_le.mp h136).le h202 (not_le.mp h207).le h209 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1762_pos (not_le.mp h136).le h202 (not_le.mp h209).le hz2 hz
        · -- right
          by_cases h210 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h211 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h212 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1721_pos (not_le.mp h202).le h201 hz1 h212 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1723_pos (not_le.mp h202).le h201 (not_le.mp h212).le h211 hz
            · -- right
              by_cases h213 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1729_pos (not_le.mp h202).le h201 (not_le.mp h211).le h213 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1731_pos (not_le.mp h202).le h201 (not_le.mp h213).le h210 hz
          · -- right
            by_cases h214 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h215 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1753_pos (not_le.mp h202).le h201 (not_le.mp h210).le h215 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1755_pos (not_le.mp h202).le h201 (not_le.mp h215).le h214 hz
            · -- right
              by_cases h216 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1761_pos (not_le.mp h202).le h201 (not_le.mp h214).le h216 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1763_pos (not_le.mp h202).le h201 (not_le.mp h216).le hz2 hz
      · -- right
        by_cases h217 : a ≤ ((1251723/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h218 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h219 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h220 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1724_pos (not_le.mp h201).le h217 hz1 h220 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1726_pos (not_le.mp h201).le h217 (not_le.mp h220).le h219 hz
            · -- right
              by_cases h221 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1732_pos (not_le.mp h201).le h217 (not_le.mp h219).le h221 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1734_pos (not_le.mp h201).le h217 (not_le.mp h221).le h218 hz
          · -- right
            by_cases h222 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h223 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1756_pos (not_le.mp h201).le h217 (not_le.mp h218).le h223 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1758_pos (not_le.mp h201).le h217 (not_le.mp h223).le h222 hz
            · -- right
              by_cases h224 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1764_pos (not_le.mp h201).le h217 (not_le.mp h222).le h224 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1766_pos (not_le.mp h201).le h217 (not_le.mp h224).le hz2 hz
        · -- right
          by_cases h225 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h226 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h227 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1725_pos (not_le.mp h217).le h200 hz1 h227 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1727_pos (not_le.mp h217).le h200 (not_le.mp h227).le h226 hz
            · -- right
              by_cases h228 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1733_pos (not_le.mp h217).le h200 (not_le.mp h226).le h228 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1735_pos (not_le.mp h217).le h200 (not_le.mp h228).le h225 hz
          · -- right
            by_cases h229 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h230 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1757_pos (not_le.mp h217).le h200 (not_le.mp h225).le h230 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1759_pos (not_le.mp h217).le h200 (not_le.mp h230).le h229 hz
            · -- right
              by_cases h231 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1765_pos (not_le.mp h217).le h200 (not_le.mp h229).le h231 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1767_pos (not_le.mp h217).le h200 (not_le.mp h231).le hz2 hz
    · -- right
      by_cases h232 : a ≤ ((125427/819200 : ℚ) : ℝ)
      · -- left
        by_cases h233 : a ≤ ((1253421/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h234 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h235 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h236 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1736_pos (not_le.mp h200).le h233 hz1 h236 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1738_pos (not_le.mp h200).le h233 (not_le.mp h236).le h235 hz
            · -- right
              by_cases h237 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1744_pos (not_le.mp h200).le h233 (not_le.mp h235).le h237 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1746_pos (not_le.mp h200).le h233 (not_le.mp h237).le h234 hz
          · -- right
            by_cases h238 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h239 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1768_pos (not_le.mp h200).le h233 (not_le.mp h234).le h239 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1770_pos (not_le.mp h200).le h233 (not_le.mp h239).le h238 hz
            · -- right
              by_cases h240 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1776_pos (not_le.mp h200).le h233 (not_le.mp h238).le h240 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1778_pos (not_le.mp h200).le h233 (not_le.mp h240).le hz2 hz
        · -- right
          by_cases h241 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h242 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h243 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B028.e1737_pos (not_le.mp h233).le h232 hz1 h243 hz
              · -- right
                exact CKLaneC2R.EpCells.B028.e1739_pos (not_le.mp h233).le h232 (not_le.mp h243).le h242 hz
            · -- right
              by_cases h244 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1745_pos (not_le.mp h233).le h232 (not_le.mp h242).le h244 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1747_pos (not_le.mp h233).le h232 (not_le.mp h244).le h241 hz
          · -- right
            by_cases h245 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h246 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1769_pos (not_le.mp h233).le h232 (not_le.mp h241).le h246 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1771_pos (not_le.mp h233).le h232 (not_le.mp h246).le h245 hz
            · -- right
              by_cases h247 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1777_pos (not_le.mp h233).le h232 (not_le.mp h245).le h247 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1779_pos (not_le.mp h233).le h232 (not_le.mp h247).le hz2 hz
      · -- right
        by_cases h248 : a ≤ ((1255119/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h249 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h250 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h251 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1740_pos (not_le.mp h232).le h248 hz1 h251 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1742_pos (not_le.mp h232).le h248 (not_le.mp h251).le h250 hz
            · -- right
              by_cases h252 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1748_pos (not_le.mp h232).le h248 (not_le.mp h250).le h252 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1750_pos (not_le.mp h232).le h248 (not_le.mp h252).le h249 hz
          · -- right
            by_cases h253 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h254 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1772_pos (not_le.mp h232).le h248 (not_le.mp h249).le h254 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1774_pos (not_le.mp h232).le h248 (not_le.mp h254).le h253 hz
            · -- right
              by_cases h255 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1780_pos (not_le.mp h232).le h248 (not_le.mp h253).le h255 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1782_pos (not_le.mp h232).le h248 (not_le.mp h255).le hz2 hz
        · -- right
          by_cases h256 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h257 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h258 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1741_pos (not_le.mp h248).le h7 hz1 h258 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1743_pos (not_le.mp h248).le h7 (not_le.mp h258).le h257 hz
            · -- right
              by_cases h259 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1749_pos (not_le.mp h248).le h7 (not_le.mp h257).le h259 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1751_pos (not_le.mp h248).le h7 (not_le.mp h259).le h256 hz
          · -- right
            by_cases h260 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h261 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1773_pos (not_le.mp h248).le h7 (not_le.mp h256).le h261 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1775_pos (not_le.mp h248).le h7 (not_le.mp h261).le h260 hz
            · -- right
              by_cases h262 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1781_pos (not_le.mp h248).le h7 (not_le.mp h260).le h262 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1783_pos (not_le.mp h248).le h7 (not_le.mp h262).le hz2 hz

end CKLaneC2R.EndpointCover


