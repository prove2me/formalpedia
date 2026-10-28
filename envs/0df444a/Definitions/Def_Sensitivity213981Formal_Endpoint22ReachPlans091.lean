-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans091
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans091
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:07:50.539443+00:00
-- url     : https://prove2.me/theorems/7839a2ab-bc0e-46ec-85e7-441608522c85
-- title:
--   Endpoint22 Reach Plans091 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans091 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan8805`, `ThreeBoundEndpoint22Reachable.plan8806`, `ThreeBoundEndpoint22Reachable.plan8807`, `ThreeBoundEndpoint22Reachable.plan8808`, `ThreeBoundEndpoint22Reachable.plan8809`, `ThreeBoundEndpoint22Reachable.plan8810`, `ThreeBoundEndpoint22Reachable.plan8742`, `ThreeBoundEndpoint22Reachable.plan8811`, `ThreeBoundEndpoint22Reachable.plan8812`, `ThreeBoundEndpoint22Reachable.plan8813`, `ThreeBoundEndpoint22Reachable.plan8814`, `ThreeBoundEndpoint22Reachable.plan8815`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans091.lean, lines 1–204.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans085
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans086
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
def plan8737 : Plan := .step choices279 bits1768 plan8276

def plan8738 : Plan := .step choices279 bits1769 plan8279

def plan8739 : Plan := .step choices279 bits1768 plan8280

def plan8740 : Plan := .step choices279 bits1770 plan8283

def plan8741 : Plan := .step choices279 bits1769 plan8284

def plan8742 : Plan := .step choices279 bits1768 plan8285

def plan8743 : Plan := .step choices279 bits1771 plan8288

def plan8744 : Plan := .step choices279 bits1770 plan8289

def plan8745 : Plan := .step choices279 bits1769 plan8290

def plan8746 : Plan := .step choices279 bits1768 plan8291

def plan8747 : Plan := .step choices279 bits1772 plan8294

def plan8748 : Plan := .step choices279 bits1768 plan8296

def plan8749 : Plan := .step choices279 bits1769 plan8297

def plan8750 : Plan := .step choices279 bits1768 plan8298

def plan8751 : Plan := .step choices279 bits1768 plan8306

def plan8752 : Plan := .step choices279 bits1769 plan8308

def plan8753 : Plan := .step choices279 bits1768 plan8309

def plan8754 : Plan := .step choices279 bits1770 plan8311

def plan8755 : Plan := .step choices279 bits1768 plan8314

def plan8756 : Plan := .step choices279 bits1769 plan8316

def plan8757 : Plan := .step choices279 bits1768 plan8317

def plan8758 : Plan := .step choices279 bits1771 plan8319

def plan8759 : Plan := .step choices279 bits1770 plan8320

def plan8760 : Plan := .step choices279 bits1769 plan8321

def plan8761 : Plan := .step choices279 bits1768 plan8322

def plan8762 : Plan := .step choices280 bits1773 plan8256

def plan8763 : Plan := .step choices280 bits1774 plan8257

def plan8764 : Plan := .step choices280 bits1773 plan8258

def plan8765 : Plan := .step choices280 bits1773 plan8259

def plan8766 : Plan := .step choices280 bits1774 plan8260

def plan8767 : Plan := .step choices280 bits1773 plan8261

def plan8768 : Plan := .step choices280 bits1775 plan8262

def plan8769 : Plan := .step choices280 bits1774 plan8263

def plan8770 : Plan := .step choices280 bits1773 plan8264

def plan8771 : Plan := .step choices280 bits1776 plan8265

def plan8772 : Plan := .step choices280 bits1773 plan8267

def plan8773 : Plan := .step choices280 bits1774 plan8268

def plan8774 : Plan := .step choices280 bits1773 plan8269

def plan8775 : Plan := .step choices280 bits1775 plan8270

def plan8776 : Plan := .step choices280 bits1774 plan8271

def plan8777 : Plan := .step choices280 bits1773 plan8272

def plan8778 : Plan := .step choices280 bits1773 plan8274

def plan8779 : Plan := .step choices280 bits1774 plan8276

def plan8780 : Plan := .step choices280 bits1773 plan8277

def plan8781 : Plan := .step choices280 bits1775 plan8279

def plan8782 : Plan := .step choices280 bits1774 plan8280

def plan8783 : Plan := .step choices280 bits1773 plan8281

def plan8784 : Plan := .step choices280 bits1776 plan8283

def plan8785 : Plan := .step choices280 bits1775 plan8284

def plan8786 : Plan := .step choices280 bits1774 plan8285

def plan8787 : Plan := .step choices280 bits1773 plan8286

def plan8788 : Plan := .step choices280 bits1777 plan8288

def plan8789 : Plan := .step choices280 bits1776 plan8289

def plan8790 : Plan := .step choices280 bits1775 plan8290

def plan8791 : Plan := .step choices280 bits1774 plan8291

def plan8792 : Plan := .step choices280 bits1773 plan8292

def plan8793 : Plan := .step choices280 bits1778 plan8294

def plan8794 : Plan := .step choices280 bits1773 plan8305

def plan8795 : Plan := .step choices280 bits1774 plan8306

def plan8796 : Plan := .step choices280 bits1773 plan8307

def plan8797 : Plan := .step choices280 bits1775 plan8308

def plan8798 : Plan := .step choices280 bits1774 plan8309

def plan8799 : Plan := .step choices280 bits1773 plan8310

def plan8800 : Plan := .step choices280 bits1776 plan8311

def plan8801 : Plan := .step choices280 bits1773 plan8313

def plan8802 : Plan := .step choices280 bits1774 plan8314

def plan8803 : Plan := .step choices280 bits1773 plan8315

def plan8804 : Plan := .step choices280 bits1775 plan8316

def plan8805 : Plan := .step choices280 bits1774 plan8317

def plan8806 : Plan := .step choices280 bits1773 plan8318

def plan8807 : Plan := .step choices280 bits1777 plan8319

def plan8808 : Plan := .step choices280 bits1776 plan8320

def plan8809 : Plan := .step choices280 bits1775 plan8321

def plan8810 : Plan := .step choices280 bits1774 plan8322

def plan8811 : Plan := .step choices280 bits1773 plan8323

def plan8812 : Plan := .step choices281 bits1779 plan8273

def plan8813 : Plan := .step choices281 bits1780 plan8274

def plan8814 : Plan := .step choices281 bits1779 plan8275

def plan8815 : Plan := .step choices281 bits1781 plan8276

def plan8816 : Plan := .step choices281 bits1780 plan8277

def plan8817 : Plan := .step choices281 bits1779 plan8278

def plan8818 : Plan := .step choices281 bits1782 plan8279

def plan8819 : Plan := .step choices281 bits1781 plan8280

def plan8820 : Plan := .step choices281 bits1780 plan8281

def plan8821 : Plan := .step choices281 bits1779 plan8282

def plan8822 : Plan := .step choices281 bits1783 plan8283

def plan8823 : Plan := .step choices281 bits1782 plan8284

def plan8824 : Plan := .step choices281 bits1781 plan8285

def plan8825 : Plan := .step choices281 bits1780 plan8286

def plan8826 : Plan := .step choices281 bits1779 plan8287

def plan8827 : Plan := .step choices281 bits1784 plan8288

def plan8828 : Plan := .step choices281 bits1783 plan8289

def plan8829 : Plan := .step choices281 bits1782 plan8290

def plan8830 : Plan := .step choices281 bits1781 plan8291

def plan8831 : Plan := .step choices281 bits1780 plan8292

def plan8832 : Plan := .step choices281 bits1779 plan8293

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


