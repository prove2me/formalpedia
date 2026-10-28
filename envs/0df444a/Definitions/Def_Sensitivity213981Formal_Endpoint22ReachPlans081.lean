-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans081
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans081
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:03:17.558994+00:00
-- url     : https://prove2.me/theorems/7354718a-a2c6-41a2-9aa8-2b8a17a7ff2f
-- title:
--   Endpoint22 Reach Plans081 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans081 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan7845`, `ThreeBoundEndpoint22Reachable.plan7846`, `ThreeBoundEndpoint22Reachable.plan7847`, `ThreeBoundEndpoint22Reachable.plan7848`, `ThreeBoundEndpoint22Reachable.plan7849`, `ThreeBoundEndpoint22Reachable.plan7850`, `ThreeBoundEndpoint22Reachable.plan7782`, `ThreeBoundEndpoint22Reachable.plan7851`, `ThreeBoundEndpoint22Reachable.plan7852`, `ThreeBoundEndpoint22Reachable.plan7853`, `ThreeBoundEndpoint22Reachable.plan7854`, `ThreeBoundEndpoint22Reachable.plan7855`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans081.lean, lines 1–204.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
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
def plan7777 : Plan := .step choices224 bits1690 plan6064

def plan7778 : Plan := .step choices224 bits1687 plan6065

def plan7779 : Plan := .step choices224 bits1687 plan6066

def plan7780 : Plan := .step choices224 bits1688 plan6067

def plan7781 : Plan := .step choices224 bits1687 plan6068

def plan7782 : Plan := .step choices224 bits1689 plan6069

def plan7783 : Plan := .step choices224 bits1688 plan6070

def plan7784 : Plan := .step choices224 bits1687 plan6071

def plan7785 : Plan := .step choices224 bits1687 plan6072

def plan7786 : Plan := .step choices224 bits1688 plan6073

def plan7787 : Plan := .step choices224 bits1687 plan6074

def plan7788 : Plan := .step choices224 bits1689 plan6075

def plan7789 : Plan := .step choices224 bits1688 plan6076

def plan7790 : Plan := .step choices224 bits1687 plan6077

def plan7791 : Plan := .step choices224 bits1690 plan6078

def plan7792 : Plan := .step choices224 bits1689 plan6079

def plan7793 : Plan := .step choices224 bits1688 plan6080

def plan7794 : Plan := .step choices224 bits1687 plan6081

def plan7795 : Plan := .step choices224 bits1691 plan6082

def plan7796 : Plan := .step choices224 bits1687 plan6084

def plan7797 : Plan := .step choices224 bits1688 plan6086

def plan7798 : Plan := .step choices224 bits1687 plan6087

def plan7799 : Plan := .step choices224 bits1689 plan6089

def plan7800 : Plan := .step choices224 bits1687 plan6091

def plan7801 : Plan := .step choices224 bits1688 plan6093

def plan7802 : Plan := .step choices224 bits1687 plan6094

def plan7803 : Plan := .step choices224 bits1690 plan6096

def plan7804 : Plan := .step choices224 bits1689 plan6097

def plan7805 : Plan := .step choices224 bits1688 plan6098

def plan7806 : Plan := .step choices224 bits1687 plan6099

def plan7807 : Plan := .step choices224 bits1692 plan6100

def plan7808 : Plan := .step choices224 bits1691 plan6101

def plan7809 : Plan := .step choices224 bits1690 plan6102

def plan7810 : Plan := .step choices224 bits1689 plan6103

def plan7811 : Plan := .step choices224 bits1688 plan6104

def plan7812 : Plan := .step choices225 bits1687 plan5995

def plan7813 : Plan := .step choices225 bits1688 plan5996

def plan7814 : Plan := .step choices225 bits1687 plan5997

def plan7815 : Plan := .step choices225 bits1687 plan5998

def plan7816 : Plan := .step choices225 bits1688 plan5999

def plan7817 : Plan := .step choices225 bits1687 plan6000

def plan7818 : Plan := .step choices225 bits1689 plan6001

def plan7819 : Plan := .step choices225 bits1688 plan6002

def plan7820 : Plan := .step choices225 bits1687 plan6003

def plan7821 : Plan := .step choices225 bits1690 plan6004

def plan7822 : Plan := .step choices225 bits1687 plan6005

def plan7823 : Plan := .step choices225 bits1688 plan6006

def plan7824 : Plan := .step choices225 bits1687 plan6007

def plan7825 : Plan := .step choices225 bits1689 plan6008

def plan7826 : Plan := .step choices225 bits1688 plan6009

def plan7827 : Plan := .step choices225 bits1687 plan6010

def plan7828 : Plan := .step choices225 bits1688 plan6011

def plan7829 : Plan := .step choices225 bits1689 plan6012

def plan7830 : Plan := .step choices225 bits1688 plan6013

def plan7831 : Plan := .step choices225 bits1690 plan6014

def plan7832 : Plan := .step choices225 bits1689 plan6015

def plan7833 : Plan := .step choices225 bits1688 plan6016

def plan7834 : Plan := .step choices225 bits1691 plan6017

def plan7835 : Plan := .step choices225 bits1690 plan6018

def plan7836 : Plan := .step choices225 bits1689 plan6019

def plan7837 : Plan := .step choices225 bits1688 plan6020

def plan7838 : Plan := .step choices225 bits1692 plan6021

def plan7839 : Plan := .step choices225 bits1687 plan6022

def plan7840 : Plan := .step choices225 bits1688 plan6023

def plan7841 : Plan := .step choices225 bits1687 plan6024

def plan7842 : Plan := .step choices225 bits1689 plan6025

def plan7843 : Plan := .step choices225 bits1688 plan6026

def plan7844 : Plan := .step choices225 bits1687 plan6027

def plan7845 : Plan := .step choices225 bits1690 plan6028

def plan7846 : Plan := .step choices225 bits1687 plan6029

def plan7847 : Plan := .step choices225 bits1688 plan6030

def plan7848 : Plan := .step choices225 bits1687 plan6031

def plan7849 : Plan := .step choices225 bits1689 plan6032

def plan7850 : Plan := .step choices225 bits1688 plan6033

def plan7851 : Plan := .step choices225 bits1687 plan6034

def plan7852 : Plan := .step choices225 bits1691 plan6035

def plan7853 : Plan := .step choices225 bits1690 plan6036

def plan7854 : Plan := .step choices225 bits1689 plan6037

def plan7855 : Plan := .step choices225 bits1688 plan6038

def plan7856 : Plan := .step choices225 bits1689 plan6039

def plan7857 : Plan := .step choices225 bits1690 plan6040

def plan7858 : Plan := .step choices225 bits1689 plan6041

def plan7859 : Plan := .step choices225 bits1691 plan6042

def plan7860 : Plan := .step choices225 bits1690 plan6043

def plan7861 : Plan := .step choices225 bits1689 plan6044

def plan7862 : Plan := .step choices225 bits1692 plan6045

def plan7863 : Plan := .step choices225 bits1691 plan6046

def plan7864 : Plan := .step choices225 bits1690 plan6047

def plan7865 : Plan := .step choices225 bits1689 plan6048

def plan7866 : Plan := .step choices225 bits1693 plan6049

def plan7867 : Plan := .step choices225 bits1692 plan6050

def plan7868 : Plan := .step choices225 bits1691 plan6051

def plan7869 : Plan := .step choices225 bits1690 plan6052

def plan7870 : Plan := .step choices225 bits1689 plan6053

def plan7871 : Plan := .step choices225 bits1694 plan6054

def plan7872 : Plan := .step choices225 bits1688 plan6072

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


