-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans095
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans095
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:06:51.987802+00:00
-- url     : https://prove2.me/theorems/89292676-64cc-46fd-a568-55080f66831a
-- title:
--   Endpoint22 Reach Plans095 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans095 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan9189`, `ThreeBoundEndpoint22Reachable.plan9190`, `ThreeBoundEndpoint22Reachable.plan9191`, `ThreeBoundEndpoint22Reachable.plan9192`, `ThreeBoundEndpoint22Reachable.plan9193`, `ThreeBoundEndpoint22Reachable.plan9126`, `ThreeBoundEndpoint22Reachable.plan9194`, `ThreeBoundEndpoint22Reachable.plan9195`, `ThreeBoundEndpoint22Reachable.plan9196`, `ThreeBoundEndpoint22Reachable.plan9197`, `ThreeBoundEndpoint22Reachable.plan9198`, `ThreeBoundEndpoint22Reachable.plan9199`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans095.lean, lines 1–204.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits014
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans087
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
def plan9121 : Plan := .step choices294 bits1800 plan8383

def plan9122 : Plan := .step choices294 bits1799 plan8384

def plan9123 : Plan := .step choices294 bits1798 plan8385

def plan9124 : Plan := .step choices294 bits1797 plan8386

def plan9125 : Plan := .step choices295 bits1803 plan8365

def plan9126 : Plan := .step choices295 bits1802 plan8382

def plan9127 : Plan := .step choices295 bits1801 plan8383

def plan9128 : Plan := .step choices295 bits1800 plan8384

def plan9129 : Plan := .step choices295 bits1799 plan8385

def plan9130 : Plan := .step choices295 bits1798 plan8386

def plan9131 : Plan := .step choices295 bits1797 plan8387

def plan9132 : Plan := .step choices296 bits1686 plan8388

def plan9133 : Plan := .step choices299 bits1750 plan8389

def plan9134 : Plan := .step choices299 bits1751 plan8390

def plan9135 : Plan := .step choices299 bits1750 plan8391

def plan9136 : Plan := .step choices304 bits1786 plan8396

def plan9137 : Plan := .step choices305 bits1790 plan8392

def plan9138 : Plan := .step choices305 bits1787 plan8393

def plan9139 : Plan := .step choices305 bits1788 plan8394

def plan9140 : Plan := .step choices305 bits1787 plan8395

def plan9141 : Plan := .step choices305 bits1789 plan8396

def plan9142 : Plan := .step choices305 bits1788 plan8397

def plan9143 : Plan := .step choices305 bits1787 plan8398

def plan9144 : Plan := .step choices314 bits1809 plan8400

def plan9145 : Plan := .step choices314 bits1810 plan8402

def plan9146 : Plan := .step choices314 bits1809 plan8403

def plan9147 : Plan := .step choices316 bits1806 plan8402

def plan9148 : Plan := .step choices317 bits1805 plan8399

def plan9149 : Plan := .step choices317 bits1806 plan8400

def plan9150 : Plan := .step choices317 bits1805 plan8401

def plan9151 : Plan := .step choices317 bits1807 plan8402

def plan9152 : Plan := .step choices317 bits1806 plan8403

def plan9153 : Plan := .step choices317 bits1805 plan8404

def plan9154 : Plan := .step choices318 bits1808 plan8402

def plan9155 : Plan := .step choices320 bits1806 plan8402

def plan9156 : Plan := .step choices321 bits1807 plan8402

def plan9157 : Plan := .step choices321 bits1806 plan8403

def plan9158 : Plan := .step choices321 bits1805 plan8404

def plan9159 : Plan := .step choices323 bits1819 plan8408

def plan9160 : Plan := .step choices324 bits1818 plan8405

def plan9161 : Plan := .step choices324 bits1819 plan8406

def plan9162 : Plan := .step choices324 bits1818 plan8407

def plan9163 : Plan := .step choices324 bits1820 plan8408

def plan9164 : Plan := .step choices324 bits1819 plan8409

def plan9165 : Plan := .step choices324 bits1818 plan8410

def plan9166 : Plan := .step choices325 bits1821 plan8408

def plan9167 : Plan := .step choices327 bits1819 plan8408

def plan9168 : Plan := .step choices328 bits1820 plan8408

def plan9169 : Plan := .step choices328 bits1819 plan8409

def plan9170 : Plan := .step choices328 bits1818 plan8410

def plan9171 : Plan := .step choices329 bits1832 plan8411

def plan9172 : Plan := .step choices296 bits1752 plan9132

def plan9173 : Plan := .step choices298 bits1791 plan9134

def plan9174 : Plan := .step choices299 bits1792 plan9133

def plan9175 : Plan := .step choices299 bits1793 plan9134

def plan9176 : Plan := .step choices299 bits1792 plan9135

def plan9177 : Plan := .step choices303 bits1812 plan9141

def plan9178 : Plan := .step choices304 bits1812 plan9136

def plan9179 : Plan := .step choices304 bits1813 plan9139

def plan9180 : Plan := .step choices304 bits1814 plan9141

def plan9181 : Plan := .step choices304 bits1813 plan9142

def plan9182 : Plan := .step choices305 bits1815 plan9138

def plan9183 : Plan := .step choices305 bits1816 plan9139

def plan9184 : Plan := .step choices305 bits1815 plan9140

def plan9185 : Plan := .step choices305 bits1817 plan9141

def plan9186 : Plan := .step choices305 bits1816 plan9142

def plan9187 : Plan := .step choices305 bits1815 plan9143

def plan9188 : Plan := .step choices306 bits1815 plan9137

def plan9189 : Plan := .step choices309 bits1815 plan9137

def plan9190 : Plan := .step choices311 bits1822 plan9154

def plan9191 : Plan := .step choices312 bits1823 plan9151

def plan9192 : Plan := .step choices312 bits1824 plan9154

def plan9193 : Plan := .step choices312 bits1823 plan9156

def plan9194 : Plan := .step choices313 bits1825 plan9147

def plan9195 : Plan := .step choices313 bits1825 plan9149

def plan9196 : Plan := .step choices313 bits1826 plan9151

def plan9197 : Plan := .step choices313 bits1825 plan9152

def plan9198 : Plan := .step choices313 bits1827 plan9154

def plan9199 : Plan := .step choices313 bits1825 plan9155

def plan9200 : Plan := .step choices313 bits1826 plan9156

def plan9201 : Plan := .step choices313 bits1825 plan9157

def plan9202 : Plan := .step choices314 bits1828 plan9148

def plan9203 : Plan := .step choices314 bits1829 plan9149

def plan9204 : Plan := .step choices314 bits1828 plan9150

def plan9205 : Plan := .step choices314 bits1830 plan9151

def plan9206 : Plan := .step choices314 bits1829 plan9152

def plan9207 : Plan := .step choices314 bits1828 plan9153

def plan9208 : Plan := .step choices314 bits1831 plan9154

def plan9209 : Plan := .step choices314 bits1830 plan9156

def plan9210 : Plan := .step choices314 bits1829 plan9157

def plan9211 : Plan := .step choices314 bits1828 plan9158

def plan9212 : Plan := .step choices315 bits1828 plan9145

def plan9213 : Plan := .step choices316 bits1828 plan9144

def plan9214 : Plan := .step choices316 bits1829 plan9145

def plan9215 : Plan := .step choices316 bits1828 plan9146

def plan9216 : Plan := .step choices319 bits1828 plan9145

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


