-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans080
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans080
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:03:46.545988+00:00
-- url     : https://prove2.me/theorems/0a51ad32-cc58-4bfd-9419-2bb324cb9167
-- title:
--   Endpoint22 Reach Plans080 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans080 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan7748`, `ThreeBoundEndpoint22Reachable.plan7749`, `ThreeBoundEndpoint22Reachable.plan7685`, `ThreeBoundEndpoint22Reachable.plan7750`, `ThreeBoundEndpoint22Reachable.plan7751`, `ThreeBoundEndpoint22Reachable.plan7752`, `ThreeBoundEndpoint22Reachable.plan7753`, `ThreeBoundEndpoint22Reachable.plan7754`, `ThreeBoundEndpoint22Reachable.plan7755`, `ThreeBoundEndpoint22Reachable.plan7756`, `ThreeBoundEndpoint22Reachable.plan7757`, `ThreeBoundEndpoint22Reachable.plan7758`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans080.lean, lines 1–207.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits012
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans060
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans062
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans063
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22Reachable
open ThreeBoundRelaxedReachable ThreeBoundRelaxed
open ThreeBoundRelaxedCompiled (Int3)
def plan7681 : Plan := .step choices222 bits1616 plan5779

def plan7682 : Plan := .step choices222 bits1620 plan5780

def plan7683 : Plan := .step choices222 bits1619 plan5781

def plan7684 : Plan := .step choices222 bits1618 plan5782

def plan7685 : Plan := .step choices222 bits1617 plan5783

def plan7686 : Plan := .step choices222 bits1616 plan5784

def plan7687 : Plan := .step choices222 bits1615 plan5927

def plan7688 : Plan := .step choices222 bits1616 plan5928

def plan7689 : Plan := .step choices222 bits1615 plan5929

def plan7690 : Plan := .step choices222 bits1617 plan5930

def plan7691 : Plan := .step choices222 bits1616 plan5931

def plan7692 : Plan := .step choices222 bits1615 plan5932

def plan7693 : Plan := .step choices222 bits1618 plan5933

def plan7694 : Plan := .step choices222 bits1617 plan5934

def plan7695 : Plan := .step choices222 bits1616 plan5935

def plan7696 : Plan := .step choices222 bits1615 plan5936

def plan7697 : Plan := .step choices222 bits1614 plan5948

def plan7698 : Plan := .step choices222 bits1615 plan5949

def plan7699 : Plan := .step choices222 bits1614 plan5950

def plan7700 : Plan := .step choices222 bits1616 plan5951

def plan7701 : Plan := .step choices222 bits1615 plan5952

def plan7702 : Plan := .step choices222 bits1614 plan5953

def plan7703 : Plan := .step choices222 bits1614 plan5961

def plan7704 : Plan := .step choices224 bits1687 plan5977

def plan7705 : Plan := .step choices224 bits1687 plan5978

def plan7706 : Plan := .step choices224 bits1688 plan5979

def plan7707 : Plan := .step choices224 bits1687 plan5980

def plan7708 : Plan := .step choices224 bits1687 plan5981

def plan7709 : Plan := .step choices224 bits1688 plan5982

def plan7710 : Plan := .step choices224 bits1687 plan5983

def plan7711 : Plan := .step choices224 bits1689 plan5984

def plan7712 : Plan := .step choices224 bits1688 plan5985

def plan7713 : Plan := .step choices224 bits1687 plan5986

def plan7714 : Plan := .step choices224 bits1690 plan5987

def plan7715 : Plan := .step choices224 bits1687 plan5988

def plan7716 : Plan := .step choices224 bits1687 plan5989

def plan7717 : Plan := .step choices224 bits1688 plan5990

def plan7718 : Plan := .step choices224 bits1687 plan5991

def plan7719 : Plan := .step choices224 bits1689 plan5992

def plan7720 : Plan := .step choices224 bits1688 plan5993

def plan7721 : Plan := .step choices224 bits1687 plan5994

def plan7722 : Plan := .step choices224 bits1687 plan5996

def plan7723 : Plan := .step choices224 bits1687 plan5999

def plan7724 : Plan := .step choices224 bits1688 plan6001

def plan7725 : Plan := .step choices224 bits1687 plan6002

def plan7726 : Plan := .step choices224 bits1689 plan6004

def plan7727 : Plan := .step choices224 bits1687 plan6006

def plan7728 : Plan := .step choices224 bits1688 plan6008

def plan7729 : Plan := .step choices224 bits1687 plan6009

def plan7730 : Plan := .step choices224 bits1687 plan6011

def plan7731 : Plan := .step choices224 bits1688 plan6012

def plan7732 : Plan := .step choices224 bits1687 plan6013

def plan7733 : Plan := .step choices224 bits1689 plan6014

def plan7734 : Plan := .step choices224 bits1688 plan6015

def plan7735 : Plan := .step choices224 bits1687 plan6016

def plan7736 : Plan := .step choices224 bits1690 plan6017

def plan7737 : Plan := .step choices224 bits1689 plan6018

def plan7738 : Plan := .step choices224 bits1688 plan6019

def plan7739 : Plan := .step choices224 bits1687 plan6020

def plan7740 : Plan := .step choices224 bits1691 plan6021

def plan7741 : Plan := .step choices224 bits1687 plan6023

def plan7742 : Plan := .step choices224 bits1688 plan6025

def plan7743 : Plan := .step choices224 bits1687 plan6026

def plan7744 : Plan := .step choices224 bits1689 plan6028

def plan7745 : Plan := .step choices224 bits1687 plan6030

def plan7746 : Plan := .step choices224 bits1688 plan6032

def plan7747 : Plan := .step choices224 bits1687 plan6033

def plan7748 : Plan := .step choices224 bits1690 plan6035

def plan7749 : Plan := .step choices224 bits1689 plan6036

def plan7750 : Plan := .step choices224 bits1688 plan6037

def plan7751 : Plan := .step choices224 bits1687 plan6038

def plan7752 : Plan := .step choices224 bits1688 plan6039

def plan7753 : Plan := .step choices224 bits1689 plan6040

def plan7754 : Plan := .step choices224 bits1688 plan6041

def plan7755 : Plan := .step choices224 bits1690 plan6042

def plan7756 : Plan := .step choices224 bits1689 plan6043

def plan7757 : Plan := .step choices224 bits1688 plan6044

def plan7758 : Plan := .step choices224 bits1691 plan6045

def plan7759 : Plan := .step choices224 bits1690 plan6046

def plan7760 : Plan := .step choices224 bits1689 plan6047

def plan7761 : Plan := .step choices224 bits1688 plan6048

def plan7762 : Plan := .step choices224 bits1692 plan6049

def plan7763 : Plan := .step choices224 bits1691 plan6050

def plan7764 : Plan := .step choices224 bits1690 plan6051

def plan7765 : Plan := .step choices224 bits1689 plan6052

def plan7766 : Plan := .step choices224 bits1688 plan6053

def plan7767 : Plan := .step choices224 bits1693 plan6054

def plan7768 : Plan := .step choices224 bits1687 plan6055

def plan7769 : Plan := .step choices224 bits1688 plan6056

def plan7770 : Plan := .step choices224 bits1687 plan6057

def plan7771 : Plan := .step choices224 bits1687 plan6058

def plan7772 : Plan := .step choices224 bits1688 plan6059

def plan7773 : Plan := .step choices224 bits1687 plan6060

def plan7774 : Plan := .step choices224 bits1689 plan6061

def plan7775 : Plan := .step choices224 bits1688 plan6062

def plan7776 : Plan := .step choices224 bits1687 plan6063

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


