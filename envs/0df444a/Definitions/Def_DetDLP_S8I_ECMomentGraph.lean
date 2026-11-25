-- Prove2me | Definitions.Def_DetDLP_S8I_ECMomentGraph
-- name    : DetDLP_S8I_ECMomentGraph
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T13:17:28.335801+00:00
-- url     : https://prove2.me/theorems/442c4ad0-6b20-43ff-a8fc-ff91038e88db
-- title:
--   DetDLP S8I ECMomentGraph
-- statement:
--   Word encodings and TagSpec packaging for elliptic-curve Stage I moment queries (tag 2) in Theorem 3.1.
-- source:
--   Liu–Zhang–Ren Formal Paper, Theorem 3.1

import Definitions.Def_DetDLP_S8I_ECQueryCount
import Definitions.Def_DetDLP_S8C_TagSpec
import Definitions.Def_DetDLP_W1_Queries

set_option autoImplicit false
namespace DetDLP.S8I.ECMoment
open M89S1
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

variable {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))

def word (j : Fin 4) (T : ℕ) (η : List Bool) :=
  queryWord 2 (encodeCurveInput p E) [countWord j.val,countWord T,η]

/-- The outer tag can be read before inspecting the query's dependent indices. -/
theorem tagIntro (make port : List Bool → List Bool) (L : ℕ) (hm : Groundwork.PolyT make)
    (he : Groundwork.PolyT port)
    (h : ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
      ∀ (j : Fin 4) (T : ℕ) (η : List Bool), T ≤ p →
      η.length ≤ blockCount (bitLen p)*4*bitLen p →
      S8C.Realizes make port L (word E j T η) (bitLen p)
        (S8I.ECQueryCount.value p (blockCount (bitLen p)) E T η j)) :
    S8C.TagSpec [2] := by
  refine ⟨make,port,L,hm,he,?_⟩
  rintro t ht base payload b n hq
  obtain rfl : t = 2 := by simpa using ht
  generalize hw : queryWord 2 base payload = w at hq ⊢
  have tag : Groundwork.PolyT.bval (DetDLP_W1_Queries.first w) = 2 := by subst w; simp [queryWord]
  cases hq <;> simp only [queryWord,DetDLP_W1_Queries.first_cons,id_eq,DetDLP_W1_Queries.decode_count] at tag
  all_goals first | contradiction | exact h _ (by assumption) _ _ _ _ (by assumption) (by assumption)

end DetDLP.S8I.ECMoment


