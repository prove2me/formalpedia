-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans074
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans074
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:01:01.693632+00:00
-- url     : https://prove2.me/theorems/3b28a956-03a6-4618-aa27-2530e6769e87
-- title:
--   Endpoint22 Reach Plans074 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans074 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan7172`, `ThreeBoundEndpoint22Reachable.plan7173`, `ThreeBoundEndpoint22Reachable.plan7109`, `ThreeBoundEndpoint22Reachable.plan7174`, `ThreeBoundEndpoint22Reachable.plan7175`, `ThreeBoundEndpoint22Reachable.plan7176`, `ThreeBoundEndpoint22Reachable.plan7177`, `ThreeBoundEndpoint22Reachable.plan7178`, `ThreeBoundEndpoint22Reachable.plan7179`, `ThreeBoundEndpoint22Reachable.plan7180`, `ThreeBoundEndpoint22Reachable.plan7181`, `ThreeBoundEndpoint22Reachable.plan7182`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans074.lean, lines 1–207.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits011
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits012
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans060
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
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
def plan7105 : Plan := .step choices210 bits1519 plan5629

def plan7106 : Plan := .step choices210 bits1516 plan5630

def plan7107 : Plan := .step choices210 bits1513 plan5631

def plan7108 : Plan := .step choices210 bits1510 plan5662

def plan7109 : Plan := .step choices210 bits1512 plan5663

def plan7110 : Plan := .step choices210 bits1510 plan5664

def plan7111 : Plan := .step choices210 bits1515 plan5665

def plan7112 : Plan := .step choices210 bits1512 plan5666

def plan7113 : Plan := .step choices210 bits1510 plan5667

def plan7114 : Plan := .step choices210 bits1509 plan5679

def plan7115 : Plan := .step choices210 bits1509 plan5690

def plan7116 : Plan := .step choices210 bits1479 plan5699

def plan7117 : Plan := .step choices210 bits1492 plan5703

def plan7118 : Plan := .step choices210 bits1496 plan5704

def plan7119 : Plan := .step choices210 bits1492 plan5705

def plan7120 : Plan := .step choices210 bits1510 plan5714

def plan7121 : Plan := .step choices210 bits1512 plan5715

def plan7122 : Plan := .step choices210 bits1510 plan5716

def plan7123 : Plan := .step choices210 bits1515 plan5717

def plan7124 : Plan := .step choices210 bits1512 plan5718

def plan7125 : Plan := .step choices210 bits1510 plan5719

def plan7126 : Plan := .step choices210 bits1509 plan5731

def plan7127 : Plan := .step choices211 bits1531 plan5622

def plan7128 : Plan := .step choices211 bits1533 plan5623

def plan7129 : Plan := .step choices211 bits1531 plan5624

def plan7130 : Plan := .step choices211 bits1535 plan5625

def plan7131 : Plan := .step choices211 bits1533 plan5626

def plan7132 : Plan := .step choices211 bits1531 plan5627

def plan7133 : Plan := .step choices211 bits1537 plan5628

def plan7134 : Plan := .step choices211 bits1535 plan5629

def plan7135 : Plan := .step choices211 bits1533 plan5630

def plan7136 : Plan := .step choices211 bits1531 plan5631

def plan7137 : Plan := .step choices211 bits1529 plan5714

def plan7138 : Plan := .step choices211 bits1530 plan5715

def plan7139 : Plan := .step choices211 bits1529 plan5716

def plan7140 : Plan := .step choices211 bits1532 plan5717

def plan7141 : Plan := .step choices211 bits1530 plan5718

def plan7142 : Plan := .step choices211 bits1529 plan5719

def plan7143 : Plan := .step choices211 bits1527 plan5730

def plan7144 : Plan := .step choices211 bits1528 plan5731

def plan7145 : Plan := .step choices211 bits1527 plan5732

def plan7146 : Plan := .step choices213 bits1593 plan5797

def plan7147 : Plan := .step choices213 bits1593 plan5800

def plan7148 : Plan := .step choices213 bits1594 plan5802

def plan7149 : Plan := .step choices213 bits1593 plan5803

def plan7150 : Plan := .step choices213 bits1595 plan5805

def plan7151 : Plan := .step choices213 bits1593 plan5809

def plan7152 : Plan := .step choices213 bits1594 plan5811

def plan7153 : Plan := .step choices213 bits1593 plan5812

def plan7154 : Plan := .step choices213 bits1593 plan5837

def plan7155 : Plan := .step choices213 bits1594 plan5840

def plan7156 : Plan := .step choices213 bits1593 plan5845

def plan7157 : Plan := .step choices213 bits1593 plan5849

def plan7158 : Plan := .step choices213 bits1594 plan5851

def plan7159 : Plan := .step choices213 bits1593 plan5852

def plan7160 : Plan := .step choices213 bits1595 plan5854

def plan7161 : Plan := .step choices213 bits1594 plan5855

def plan7162 : Plan := .step choices213 bits1593 plan5856

def plan7163 : Plan := .step choices213 bits1596 plan5858

def plan7164 : Plan := .step choices213 bits1593 plan5868

def plan7165 : Plan := .step choices213 bits1594 plan5871

def plan7166 : Plan := .step choices213 bits1593 plan5876

def plan7167 : Plan := .step choices213 bits1595 plan5879

def plan7168 : Plan := .step choices213 bits1594 plan5880

def plan7169 : Plan := .step choices213 bits1593 plan5881

def plan7170 : Plan := .step choices213 bits1593 plan5883

def plan7171 : Plan := .step choices213 bits1594 plan5884

def plan7172 : Plan := .step choices213 bits1593 plan5885

def plan7173 : Plan := .step choices213 bits1595 plan5886

def plan7174 : Plan := .step choices213 bits1594 plan5887

def plan7175 : Plan := .step choices213 bits1593 plan5888

def plan7176 : Plan := .step choices213 bits1596 plan5889

def plan7177 : Plan := .step choices213 bits1595 plan5890

def plan7178 : Plan := .step choices213 bits1594 plan5891

def plan7179 : Plan := .step choices213 bits1593 plan5892

def plan7180 : Plan := .step choices213 bits1597 plan5893

def plan7181 : Plan := .step choices213 bits1596 plan5894

def plan7182 : Plan := .step choices213 bits1595 plan5895

def plan7183 : Plan := .step choices213 bits1594 plan5896

def plan7184 : Plan := .step choices213 bits1593 plan5897

def plan7185 : Plan := .step choices213 bits1598 plan5898

def plan7186 : Plan := .step choices213 bits1593 plan5910

def plan7187 : Plan := .step choices213 bits1593 plan5913

def plan7188 : Plan := .step choices213 bits1594 plan5915

def plan7189 : Plan := .step choices213 bits1593 plan5916

def plan7190 : Plan := .step choices213 bits1595 plan5918

def plan7191 : Plan := .step choices213 bits1593 plan5922

def plan7192 : Plan := .step choices213 bits1594 plan5924

def plan7193 : Plan := .step choices213 bits1593 plan5925

def plan7194 : Plan := .step choices213 bits1593 plan5938

def plan7195 : Plan := .step choices213 bits1594 plan5940

def plan7196 : Plan := .step choices213 bits1593 plan5941

def plan7197 : Plan := .step choices213 bits1595 plan5943

def plan7198 : Plan := .step choices213 bits1594 plan5944

def plan7199 : Plan := .step choices213 bits1593 plan5945

def plan7200 : Plan := .step choices213 bits1596 plan5947

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


