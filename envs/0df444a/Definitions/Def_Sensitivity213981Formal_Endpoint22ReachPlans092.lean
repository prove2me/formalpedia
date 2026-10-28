-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans092
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans092
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:07:51.328454+00:00
-- url     : https://prove2.me/theorems/bbc0911b-fb98-4f5f-b194-3f40465434dd
-- title:
--   Endpoint22 Reach Plans092 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans092 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan8901`, `ThreeBoundEndpoint22Reachable.plan8902`, `ThreeBoundEndpoint22Reachable.plan8903`, `ThreeBoundEndpoint22Reachable.plan8904`, `ThreeBoundEndpoint22Reachable.plan8905`, `ThreeBoundEndpoint22Reachable.plan8906`, `ThreeBoundEndpoint22Reachable.plan8838`, `ThreeBoundEndpoint22Reachable.plan8907`, `ThreeBoundEndpoint22Reachable.plan8908`, `ThreeBoundEndpoint22Reachable.plan8909`, `ThreeBoundEndpoint22Reachable.plan8910`, `ThreeBoundEndpoint22Reachable.plan8911`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans092.lean, lines 1–204.

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
def plan8833 : Plan := .step choices281 bits1785 plan8294

def plan8834 : Plan := .step choices281 bits1784 plan8319

def plan8835 : Plan := .step choices281 bits1783 plan8320

def plan8836 : Plan := .step choices281 bits1782 plan8321

def plan8837 : Plan := .step choices281 bits1781 plan8322

def plan8838 : Plan := .step choices281 bits1780 plan8323

def plan8839 : Plan := .step choices281 bits1779 plan8324

def plan8840 : Plan := .step choices282 bits1773 plan8222

def plan8841 : Plan := .step choices282 bits1773 plan8223

def plan8842 : Plan := .step choices282 bits1774 plan8224

def plan8843 : Plan := .step choices282 bits1773 plan8225

def plan8844 : Plan := .step choices282 bits1775 plan8226

def plan8845 : Plan := .step choices282 bits1773 plan8227

def plan8846 : Plan := .step choices282 bits1774 plan8228

def plan8847 : Plan := .step choices282 bits1773 plan8229

def plan8848 : Plan := .step choices282 bits1779 plan8231

def plan8849 : Plan := .step choices282 bits1780 plan8233

def plan8850 : Plan := .step choices282 bits1779 plan8234

def plan8851 : Plan := .step choices282 bits1781 plan8236

def plan8852 : Plan := .step choices282 bits1780 plan8237

def plan8853 : Plan := .step choices282 bits1779 plan8238

def plan8854 : Plan := .step choices282 bits1782 plan8240

def plan8855 : Plan := .step choices282 bits1781 plan8241

def plan8856 : Plan := .step choices282 bits1780 plan8242

def plan8857 : Plan := .step choices282 bits1779 plan8243

def plan8858 : Plan := .step choices282 bits1779 plan8245

def plan8859 : Plan := .step choices282 bits1779 plan8250

def plan8860 : Plan := .step choices282 bits1780 plan8252

def plan8861 : Plan := .step choices282 bits1779 plan8253

def plan8862 : Plan := .step choices282 bits1779 plan8295

def plan8863 : Plan := .step choices282 bits1779 plan8300

def plan8864 : Plan := .step choices282 bits1780 plan8302

def plan8865 : Plan := .step choices282 bits1779 plan8303

def plan8866 : Plan := .step choices283 bits1779 plan8230

def plan8867 : Plan := .step choices283 bits1780 plan8231

def plan8868 : Plan := .step choices283 bits1779 plan8232

def plan8869 : Plan := .step choices283 bits1781 plan8233

def plan8870 : Plan := .step choices283 bits1780 plan8234

def plan8871 : Plan := .step choices283 bits1779 plan8235

def plan8872 : Plan := .step choices283 bits1782 plan8236

def plan8873 : Plan := .step choices283 bits1781 plan8237

def plan8874 : Plan := .step choices283 bits1780 plan8238

def plan8875 : Plan := .step choices283 bits1779 plan8239

def plan8876 : Plan := .step choices283 bits1783 plan8240

def plan8877 : Plan := .step choices283 bits1782 plan8241

def plan8878 : Plan := .step choices283 bits1781 plan8242

def plan8879 : Plan := .step choices283 bits1780 plan8243

def plan8880 : Plan := .step choices283 bits1779 plan8244

def plan8881 : Plan := .step choices283 bits1779 plan8249

def plan8882 : Plan := .step choices283 bits1780 plan8250

def plan8883 : Plan := .step choices283 bits1779 plan8251

def plan8884 : Plan := .step choices283 bits1781 plan8252

def plan8885 : Plan := .step choices283 bits1780 plan8253

def plan8886 : Plan := .step choices283 bits1779 plan8254

def plan8887 : Plan := .step choices283 bits1779 plan8255

def plan8888 : Plan := .step choices283 bits1779 plan8266

def plan8889 : Plan := .step choices283 bits1779 plan8299

def plan8890 : Plan := .step choices283 bits1780 plan8300

def plan8891 : Plan := .step choices283 bits1779 plan8301

def plan8892 : Plan := .step choices283 bits1781 plan8302

def plan8893 : Plan := .step choices283 bits1780 plan8303

def plan8894 : Plan := .step choices283 bits1779 plan8304

def plan8895 : Plan := .step choices283 bits1779 plan8312

def plan8896 : Plan := .step choices286 bits1773 plan8222

def plan8897 : Plan := .step choices286 bits1773 plan8223

def plan8898 : Plan := .step choices286 bits1774 plan8224

def plan8899 : Plan := .step choices286 bits1773 plan8225

def plan8900 : Plan := .step choices286 bits1775 plan8226

def plan8901 : Plan := .step choices286 bits1773 plan8227

def plan8902 : Plan := .step choices286 bits1774 plan8228

def plan8903 : Plan := .step choices286 bits1773 plan8229

def plan8904 : Plan := .step choices286 bits1779 plan8231

def plan8905 : Plan := .step choices286 bits1780 plan8233

def plan8906 : Plan := .step choices286 bits1779 plan8234

def plan8907 : Plan := .step choices286 bits1781 plan8236

def plan8908 : Plan := .step choices286 bits1780 plan8237

def plan8909 : Plan := .step choices286 bits1779 plan8238

def plan8910 : Plan := .step choices286 bits1782 plan8240

def plan8911 : Plan := .step choices286 bits1781 plan8241

def plan8912 : Plan := .step choices286 bits1780 plan8242

def plan8913 : Plan := .step choices286 bits1779 plan8243

def plan8914 : Plan := .step choices286 bits1779 plan8250

def plan8915 : Plan := .step choices286 bits1780 plan8252

def plan8916 : Plan := .step choices286 bits1779 plan8253

def plan8917 : Plan := .step choices286 bits1779 plan8295

def plan8918 : Plan := .step choices286 bits1779 plan8300

def plan8919 : Plan := .step choices286 bits1780 plan8302

def plan8920 : Plan := .step choices286 bits1779 plan8303

def plan8921 : Plan := .step choices287 bits1779 plan8230

def plan8922 : Plan := .step choices287 bits1780 plan8231

def plan8923 : Plan := .step choices287 bits1779 plan8232

def plan8924 : Plan := .step choices287 bits1781 plan8233

def plan8925 : Plan := .step choices287 bits1780 plan8234

def plan8926 : Plan := .step choices287 bits1779 plan8235

def plan8927 : Plan := .step choices287 bits1782 plan8236

def plan8928 : Plan := .step choices287 bits1781 plan8237

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


