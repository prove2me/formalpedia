-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans002
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans002
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:43:20.237339+00:00
-- url     : https://prove2.me/theorems/67989714-6b1b-4092-9368-707899367b07
-- title:
--   Endpoint22 Reach Plans002 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans002 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan198`, `ThreeBoundEndpoint22Reachable.plan266`, `ThreeBoundEndpoint22Reachable.plan267`, `ThreeBoundEndpoint22Reachable.plan268`, `ThreeBoundEndpoint22Reachable.plan269`, `ThreeBoundEndpoint22Reachable.plan270`, `ThreeBoundEndpoint22Reachable.plan271`, `ThreeBoundEndpoint22Reachable.plan272`, `ThreeBoundEndpoint22Reachable.plan273`, `ThreeBoundEndpoint22Reachable.plan274`, `ThreeBoundEndpoint22Reachable.plan275`, `ThreeBoundEndpoint22Reachable.plan199`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans002.lean, lines 1–203.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans000
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
def plan193 : Plan := .step choices17 bits65 plan22

def plan194 : Plan := .step choices17 bits65 plan23

def plan195 : Plan := .step choices18 bits65 plan19

def plan196 : Plan := .step choices18 bits65 plan20

def plan197 : Plan := .step choices18 bits65 plan23

def plan198 : Plan := .step choices19 bits65 plan15

def plan199 : Plan := .step choices19 bits65 plan16

def plan200 : Plan := .step choices20 bits65 plan16

def plan201 : Plan := .step choices23 bits65 plan15

def plan202 : Plan := .step choices23 bits65 plan16

def plan203 : Plan := .step choices24 bits65 plan16

def plan204 : Plan := .step choices26 bits91 plan24

def plan205 : Plan := .step choices26 bits91 plan25

def plan206 : Plan := .step choices26 bits91 plan26

def plan207 : Plan := .step choices26 bits91 plan27

def plan208 : Plan := .step choices26 bits91 plan28

def plan209 : Plan := .step choices26 bits91 plan29

def plan210 : Plan := .step choices26 bits91 plan30

def plan211 : Plan := .step choices27 bits91 plan25

def plan212 : Plan := .step choices27 bits91 plan26

def plan213 : Plan := .step choices27 bits91 plan27

def plan214 : Plan := .step choices27 bits91 plan29

def plan215 : Plan := .step choices27 bits91 plan30

def plan216 : Plan := .step choices28 bits91 plan26

def plan217 : Plan := .step choices28 bits91 plan27

def plan218 : Plan := .step choices28 bits91 plan30

def plan219 : Plan := .step choices29 bits91 plan27

def plan220 : Plan := .step choices30 bits91 plan25

def plan221 : Plan := .step choices30 bits91 plan26

def plan222 : Plan := .step choices30 bits91 plan27

def plan223 : Plan := .step choices30 bits91 plan28

def plan224 : Plan := .step choices30 bits91 plan29

def plan225 : Plan := .step choices30 bits91 plan30

def plan226 : Plan := .step choices31 bits91 plan26

def plan227 : Plan := .step choices31 bits91 plan27

def plan228 : Plan := .step choices31 bits91 plan29

def plan229 : Plan := .step choices31 bits91 plan30

def plan230 : Plan := .step choices32 bits91 plan27

def plan231 : Plan := .step choices32 bits91 plan30

def plan232 : Plan := .step choices34 bits51 plan31

def plan233 : Plan := .step choices34 bits52 plan32

def plan234 : Plan := .step choices34 bits52 plan33

def plan235 : Plan := .step choices35 bits53 plan32

def plan236 : Plan := .step choices35 bits53 plan33

def plan237 : Plan := .step choices36 bits53 plan33

def plan238 : Plan := .step choices38 bits66 plan36

def plan239 : Plan := .step choices38 bits68 plan37

def plan240 : Plan := .step choices38 bits68 plan38

def plan241 : Plan := .step choices38 bits68 plan39

def plan242 : Plan := .step choices38 bits66 plan40

def plan243 : Plan := .step choices38 bits68 plan41

def plan244 : Plan := .step choices38 bits68 plan42

def plan245 : Plan := .step choices39 bits85 plan34

def plan246 : Plan := .step choices39 bits85 plan35

def plan247 : Plan := .step choices39 bits69 plan37

def plan248 : Plan := .step choices39 bits69 plan38

def plan249 : Plan := .step choices39 bits69 plan39

def plan250 : Plan := .step choices39 bits69 plan41

def plan251 : Plan := .step choices39 bits69 plan42

def plan252 : Plan := .step choices40 bits85 plan35

def plan253 : Plan := .step choices40 bits69 plan38

def plan254 : Plan := .step choices40 bits69 plan39

def plan255 : Plan := .step choices40 bits69 plan42

def plan256 : Plan := .step choices41 bits67 plan34

def plan257 : Plan := .step choices41 bits67 plan35

def plan258 : Plan := .step choices42 bits69 plan35

def plan259 : Plan := .step choices45 bits67 plan34

def plan260 : Plan := .step choices45 bits67 plan35

def plan261 : Plan := .step choices46 bits69 plan35

def plan262 : Plan := .step choices50 bits110 plan46

def plan263 : Plan := .step choices50 bits110 plan47

def plan264 : Plan := .step choices50 bits110 plan48

def plan265 : Plan := .step choices50 bits110 plan50

def plan266 : Plan := .step choices50 bits110 plan51

def plan267 : Plan := .step choices51 bits110 plan47

def plan268 : Plan := .step choices51 bits110 plan48

def plan269 : Plan := .step choices51 bits110 plan51

def plan270 : Plan := .step choices52 bits109 plan43

def plan271 : Plan := .step choices52 bits109 plan44

def plan272 : Plan := .step choices52 bits92 plan45

def plan273 : Plan := .step choices52 bits93 plan46

def plan274 : Plan := .step choices52 bits93 plan47

def plan275 : Plan := .step choices52 bits93 plan48

def plan276 : Plan := .step choices52 bits92 plan49

def plan277 : Plan := .step choices52 bits93 plan50

def plan278 : Plan := .step choices52 bits93 plan51

def plan279 : Plan := .step choices53 bits110 plan44

def plan280 : Plan := .step choices53 bits94 plan46

def plan281 : Plan := .step choices53 bits94 plan47

def plan282 : Plan := .step choices53 bits94 plan48

def plan283 : Plan := .step choices53 bits94 plan50

def plan284 : Plan := .step choices53 bits94 plan51

def plan285 : Plan := .step choices54 bits94 plan47

def plan286 : Plan := .step choices54 bits94 plan48

def plan287 : Plan := .step choices54 bits94 plan51

def plan288 : Plan := .step choices55 bits94 plan48

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


