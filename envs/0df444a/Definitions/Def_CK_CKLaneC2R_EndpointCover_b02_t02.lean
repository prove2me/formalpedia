-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b02_t02
-- name    : CK_CKLaneC2R_EndpointCover_b02_t02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T08:53:09.999817+00:00
-- url     : https://prove2.me/theorems/990470b2-ff5f-45d2-8048-f2889b4429f3
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 3 of 4 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 3 of 4 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 3 of 4 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 3 of 4 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 3 of 4 of 2).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B010__2
import Definitions.Def_CK_CKLaneC2R_EpCells_B012
import Definitions.Def_CK_CKLaneC2R_EpCells_B013
namespace CKLaneC2R.EndpointCover

theorem cover_sub_012 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : a ≤ ((3249/16000 : ℚ) : ℝ)) (h4 : ¬ (a ≤ ((5649/32000 : ℚ) : ℝ))) (h1613 : a ≤ ((12147/64000 : ℚ) : ℝ)) (h1614 : a ≤ ((4689/25600 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1615 : a ≤ ((46041/256000 : ℚ) : ℝ)
  · -- left
    by_cases h1616 : a ≤ ((91233/512000 : ℚ) : ℝ)
    · -- left
      by_cases h1617 : a ≤ ((181617/1024000 : ℚ) : ℝ)
      · -- left
        by_cases h1618 : a ≤ ((72477/409600 : ℚ) : ℝ)
        · -- left
          by_cases h1619 : a ≤ ((723921/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1620 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1621 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e701_pos (not_le.mp h4).le h1619 hz1 h1621 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e703_pos (not_le.mp h4).le h1619 (not_le.mp h1621).le h1620 hz
            · -- right
              by_cases h1622 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e709_pos (not_le.mp h4).le h1619 (not_le.mp h1620).le h1622 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e711_pos (not_le.mp h4).le h1619 (not_le.mp h1622).le hz2 hz
          · -- right
            by_cases h1623 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1624 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e702_pos (not_le.mp h1619).le h1618 hz1 h1624 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e704_pos (not_le.mp h1619).le h1618 (not_le.mp h1624).le h1623 hz
            · -- right
              by_cases h1625 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e710_pos (not_le.mp h1619).le h1618 (not_le.mp h1623).le h1625 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e712_pos (not_le.mp h1619).le h1618 (not_le.mp h1625).le hz2 hz
        · -- right
          by_cases h1626 : a ≤ ((725619/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1627 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1628 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e705_pos (not_le.mp h1618).le h1626 hz1 h1628 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e707_pos (not_le.mp h1618).le h1626 (not_le.mp h1628).le h1627 hz
            · -- right
              by_cases h1629 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e713_pos (not_le.mp h1618).le h1626 (not_le.mp h1627).le h1629 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e715_pos (not_le.mp h1618).le h1626 (not_le.mp h1629).le hz2 hz
          · -- right
            by_cases h1630 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1631 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e706_pos (not_le.mp h1626).le h1617 hz1 h1631 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e708_pos (not_le.mp h1626).le h1617 (not_le.mp h1631).le h1630 hz
            · -- right
              by_cases h1632 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e714_pos (not_le.mp h1626).le h1617 (not_le.mp h1630).le h1632 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e716_pos (not_le.mp h1626).le h1617 (not_le.mp h1632).le hz2 hz
      · -- right
        by_cases h1633 : a ≤ ((364083/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h1634 : a ≤ ((727317/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1635 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1636 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e717_pos (not_le.mp h1617).le h1634 hz1 h1636 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e719_pos (not_le.mp h1617).le h1634 (not_le.mp h1636).le h1635 hz
            · -- right
              by_cases h1637 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e725_pos (not_le.mp h1617).le h1634 (not_le.mp h1635).le h1637 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e727_pos (not_le.mp h1617).le h1634 (not_le.mp h1637).le hz2 hz
          · -- right
            by_cases h1638 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1639 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e718_pos (not_le.mp h1634).le h1633 hz1 h1639 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e720_pos (not_le.mp h1634).le h1633 (not_le.mp h1639).le h1638 hz
            · -- right
              by_cases h1640 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e726_pos (not_le.mp h1634).le h1633 (not_le.mp h1638).le h1640 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e728_pos (not_le.mp h1634).le h1633 (not_le.mp h1640).le hz2 hz
        · -- right
          by_cases h1641 : a ≤ ((145803/819200 : ℚ) : ℝ)
          · -- left
            by_cases h1642 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1643 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e721_pos (not_le.mp h1633).le h1641 hz1 h1643 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e723_pos (not_le.mp h1633).le h1641 (not_le.mp h1643).le h1642 hz
            · -- right
              by_cases h1644 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e729_pos (not_le.mp h1633).le h1641 (not_le.mp h1642).le h1644 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e731_pos (not_le.mp h1633).le h1641 (not_le.mp h1644).le hz2 hz
          · -- right
            by_cases h1645 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1646 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e722_pos (not_le.mp h1641).le h1616 hz1 h1646 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e724_pos (not_le.mp h1641).le h1616 (not_le.mp h1646).le h1645 hz
            · -- right
              by_cases h1647 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e730_pos (not_le.mp h1641).le h1616 (not_le.mp h1645).le h1647 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e732_pos (not_le.mp h1641).le h1616 (not_le.mp h1647).le hz2 hz
    · -- right
      by_cases h1648 : a ≤ ((36663/204800 : ℚ) : ℝ)
      · -- left
        by_cases h1649 : a ≤ ((365781/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h1650 : a ≤ ((730713/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1651 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1652 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e733_pos (not_le.mp h1616).le h1650 hz1 h1652 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e735_pos (not_le.mp h1616).le h1650 (not_le.mp h1652).le h1651 hz
            · -- right
              by_cases h1653 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e741_pos (not_le.mp h1616).le h1650 (not_le.mp h1651).le h1653 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e743_pos (not_le.mp h1616).le h1650 (not_le.mp h1653).le hz2 hz
          · -- right
            by_cases h1654 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1655 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e734_pos (not_le.mp h1650).le h1649 hz1 h1655 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e736_pos (not_le.mp h1650).le h1649 (not_le.mp h1655).le h1654 hz
            · -- right
              by_cases h1656 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e742_pos (not_le.mp h1650).le h1649 (not_le.mp h1654).le h1656 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e744_pos (not_le.mp h1650).le h1649 (not_le.mp h1656).le hz2 hz
        · -- right
          by_cases h1657 : a ≤ ((732411/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1658 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1659 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e737_pos (not_le.mp h1649).le h1657 hz1 h1659 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e739_pos (not_le.mp h1649).le h1657 (not_le.mp h1659).le h1658 hz
            · -- right
              by_cases h1660 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e745_pos (not_le.mp h1649).le h1657 (not_le.mp h1658).le h1660 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e747_pos (not_le.mp h1649).le h1657 (not_le.mp h1660).le hz2 hz
          · -- right
            by_cases h1661 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1662 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e738_pos (not_le.mp h1657).le h1648 hz1 h1662 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e740_pos (not_le.mp h1657).le h1648 (not_le.mp h1662).le h1661 hz
            · -- right
              by_cases h1663 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e746_pos (not_le.mp h1657).le h1648 (not_le.mp h1661).le h1663 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e748_pos (not_le.mp h1657).le h1648 (not_le.mp h1663).le hz2 hz
      · -- right
        by_cases h1664 : a ≤ ((367479/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h1665 : a ≤ ((734109/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1666 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1667 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e749_pos (not_le.mp h1648).le h1665 hz1 h1667 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e751_pos (not_le.mp h1648).le h1665 (not_le.mp h1667).le h1666 hz
            · -- right
              by_cases h1668 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e757_pos (not_le.mp h1648).le h1665 (not_le.mp h1666).le h1668 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e759_pos (not_le.mp h1648).le h1665 (not_le.mp h1668).le hz2 hz
          · -- right
            by_cases h1669 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1670 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e750_pos (not_le.mp h1665).le h1664 hz1 h1670 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e752_pos (not_le.mp h1665).le h1664 (not_le.mp h1670).le h1669 hz
            · -- right
              by_cases h1671 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e758_pos (not_le.mp h1665).le h1664 (not_le.mp h1669).le h1671 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e760_pos (not_le.mp h1665).le h1664 (not_le.mp h1671).le hz2 hz
        · -- right
          by_cases h1672 : a ≤ ((735807/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1673 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1674 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e753_pos (not_le.mp h1664).le h1672 hz1 h1674 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e755_pos (not_le.mp h1664).le h1672 (not_le.mp h1674).le h1673 hz
            · -- right
              by_cases h1675 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e761_pos (not_le.mp h1664).le h1672 (not_le.mp h1673).le h1675 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e763_pos (not_le.mp h1664).le h1672 (not_le.mp h1675).le hz2 hz
          · -- right
            by_cases h1676 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1677 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e754_pos (not_le.mp h1672).le h1615 hz1 h1677 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e756_pos (not_le.mp h1672).le h1615 (not_le.mp h1677).le h1676 hz
            · -- right
              by_cases h1678 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e762_pos (not_le.mp h1672).le h1615 (not_le.mp h1676).le h1678 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e764_pos (not_le.mp h1672).le h1615 (not_le.mp h1678).le hz2 hz
  · -- right
    by_cases h1679 : a ≤ ((92931/512000 : ℚ) : ℝ)
    · -- left
      by_cases h1680 : a ≤ ((185013/1024000 : ℚ) : ℝ)
      · -- left
        by_cases h1681 : a ≤ ((369177/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h1682 : a ≤ ((147501/819200 : ℚ) : ℝ)
          · -- left
            by_cases h1683 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1684 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e765_pos (not_le.mp h1615).le h1682 hz1 h1684 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e767_pos (not_le.mp h1615).le h1682 (not_le.mp h1684).le h1683 hz
            · -- right
              by_cases h1685 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e773_pos (not_le.mp h1615).le h1682 (not_le.mp h1683).le h1685 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e775_pos (not_le.mp h1615).le h1682 (not_le.mp h1685).le hz2 hz
          · -- right
            by_cases h1686 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1687 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e766_pos (not_le.mp h1682).le h1681 hz1 h1687 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e768_pos (not_le.mp h1682).le h1681 (not_le.mp h1687).le h1686 hz
            · -- right
              by_cases h1688 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e774_pos (not_le.mp h1682).le h1681 (not_le.mp h1686).le h1688 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e776_pos (not_le.mp h1682).le h1681 (not_le.mp h1688).le hz2 hz
        · -- right
          by_cases h1689 : a ≤ ((739203/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1690 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1691 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e769_pos (not_le.mp h1681).le h1689 hz1 h1691 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e771_pos (not_le.mp h1681).le h1689 (not_le.mp h1691).le h1690 hz
            · -- right
              by_cases h1692 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e777_pos (not_le.mp h1681).le h1689 (not_le.mp h1690).le h1692 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e779_pos (not_le.mp h1681).le h1689 (not_le.mp h1692).le hz2 hz
          · -- right
            by_cases h1693 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1694 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e770_pos (not_le.mp h1689).le h1680 hz1 h1694 hz
              · -- right
                exact CKLaneC2R.EpCells.B012.e772_pos (not_le.mp h1689).le h1680 (not_le.mp h1694).le h1693 hz
            · -- right
              by_cases h1695 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B012.e778_pos (not_le.mp h1689).le h1680 (not_le.mp h1693).le h1695 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e780_pos (not_le.mp h1689).le h1680 (not_le.mp h1695).le hz2 hz
      · -- right
        by_cases h1696 : a ≤ ((2967/16384 : ℚ) : ℝ)
        · -- left
          by_cases h1697 : a ≤ ((740901/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1698 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1699 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e781_pos (not_le.mp h1680).le h1697 hz1 h1699 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e783_pos (not_le.mp h1680).le h1697 (not_le.mp h1699).le h1698 hz
            · -- right
              by_cases h1700 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e789_pos (not_le.mp h1680).le h1697 (not_le.mp h1698).le h1700 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e791_pos (not_le.mp h1680).le h1697 (not_le.mp h1700).le hz2 hz
          · -- right
            by_cases h1701 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1702 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e782_pos (not_le.mp h1697).le h1696 hz1 h1702 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e784_pos (not_le.mp h1697).le h1696 (not_le.mp h1702).le h1701 hz
            · -- right
              by_cases h1703 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e790_pos (not_le.mp h1697).le h1696 (not_le.mp h1701).le h1703 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e792_pos (not_le.mp h1697).le h1696 (not_le.mp h1703).le hz2 hz
        · -- right
          by_cases h1704 : a ≤ ((742599/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1705 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1706 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e785_pos (not_le.mp h1696).le h1704 hz1 h1706 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e787_pos (not_le.mp h1696).le h1704 (not_le.mp h1706).le h1705 hz
            · -- right
              by_cases h1707 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e793_pos (not_le.mp h1696).le h1704 (not_le.mp h1705).le h1707 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e795_pos (not_le.mp h1696).le h1704 (not_le.mp h1707).le hz2 hz
          · -- right
            by_cases h1708 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1709 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e786_pos (not_le.mp h1704).le h1679 hz1 h1709 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e788_pos (not_le.mp h1704).le h1679 (not_le.mp h1709).le h1708 hz
            · -- right
              by_cases h1710 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e794_pos (not_le.mp h1704).le h1679 (not_le.mp h1708).le h1710 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e796_pos (not_le.mp h1704).le h1679 (not_le.mp h1710).le hz2 hz
    · -- right
      by_cases h1711 : a ≤ ((186711/1024000 : ℚ) : ℝ)
      · -- left
        by_cases h1712 : a ≤ ((372573/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h1713 : a ≤ ((744297/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1714 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1715 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e797_pos (not_le.mp h1679).le h1713 hz1 h1715 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e799_pos (not_le.mp h1679).le h1713 (not_le.mp h1715).le h1714 hz
            · -- right
              by_cases h1716 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e805_pos (not_le.mp h1679).le h1713 (not_le.mp h1714).le h1716 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e807_pos (not_le.mp h1679).le h1713 (not_le.mp h1716).le hz2 hz
          · -- right
            by_cases h1717 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1718 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e798_pos (not_le.mp h1713).le h1712 hz1 h1718 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e800_pos (not_le.mp h1713).le h1712 (not_le.mp h1718).le h1717 hz
            · -- right
              by_cases h1719 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e806_pos (not_le.mp h1713).le h1712 (not_le.mp h1717).le h1719 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e808_pos (not_le.mp h1713).le h1712 (not_le.mp h1719).le hz2 hz
        · -- right
          by_cases h1720 : a ≤ ((149199/819200 : ℚ) : ℝ)
          · -- left
            by_cases h1721 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1722 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e801_pos (not_le.mp h1712).le h1720 hz1 h1722 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e803_pos (not_le.mp h1712).le h1720 (not_le.mp h1722).le h1721 hz
            · -- right
              by_cases h1723 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e809_pos (not_le.mp h1712).le h1720 (not_le.mp h1721).le h1723 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e811_pos (not_le.mp h1712).le h1720 (not_le.mp h1723).le hz2 hz
          · -- right
            by_cases h1724 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1725 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e802_pos (not_le.mp h1720).le h1711 hz1 h1725 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e804_pos (not_le.mp h1720).le h1711 (not_le.mp h1725).le h1724 hz
            · -- right
              by_cases h1726 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e810_pos (not_le.mp h1720).le h1711 (not_le.mp h1724).le h1726 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e812_pos (not_le.mp h1720).le h1711 (not_le.mp h1726).le hz2 hz
      · -- right
        by_cases h1727 : a ≤ ((374271/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h1728 : a ≤ ((747693/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1729 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1730 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e813_pos (not_le.mp h1711).le h1728 hz1 h1730 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e815_pos (not_le.mp h1711).le h1728 (not_le.mp h1730).le h1729 hz
            · -- right
              by_cases h1731 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e821_pos (not_le.mp h1711).le h1728 (not_le.mp h1729).le h1731 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e823_pos (not_le.mp h1711).le h1728 (not_le.mp h1731).le hz2 hz
          · -- right
            by_cases h1732 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1733 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e814_pos (not_le.mp h1728).le h1727 hz1 h1733 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e816_pos (not_le.mp h1728).le h1727 (not_le.mp h1733).le h1732 hz
            · -- right
              by_cases h1734 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e822_pos (not_le.mp h1728).le h1727 (not_le.mp h1732).le h1734 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e824_pos (not_le.mp h1728).le h1727 (not_le.mp h1734).le hz2 hz
        · -- right
          by_cases h1735 : a ≤ ((749391/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1736 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1737 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e817_pos (not_le.mp h1727).le h1735 hz1 h1737 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e819_pos (not_le.mp h1727).le h1735 (not_le.mp h1737).le h1736 hz
            · -- right
              by_cases h1738 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e825_pos (not_le.mp h1727).le h1735 (not_le.mp h1736).le h1738 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e827_pos (not_le.mp h1727).le h1735 (not_le.mp h1738).le hz2 hz
          · -- right
            by_cases h1739 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1740 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e818_pos (not_le.mp h1735).le h1614 hz1 h1740 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e820_pos (not_le.mp h1735).le h1614 (not_le.mp h1740).le h1739 hz
            · -- right
              by_cases h1741 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e826_pos (not_le.mp h1735).le h1614 (not_le.mp h1739).le h1741 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e828_pos (not_le.mp h1735).le h1614 (not_le.mp h1741).le hz2 hz

end CKLaneC2R.EndpointCover


