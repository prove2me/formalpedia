-- Prove2me | Definitions.Def_DetDLP_S8H_ECElemGraph
-- name    : DetDLP_S8H_ECElemGraph
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T13:30:50.506628+00:00
-- url     : https://prove2.me/theorems/936c5d9f-5234-45c8-81b5-47d01d008676
-- title:
--   DetDLP S8H ECElemGraph
-- statement:
--   Word encodings, semantic counts, and TagSpec packaging for elliptic-curve Stage I element queries (tag 4) in Theorem 3.1.
-- source:
--   Liu–Zhang–Ren Formal Paper, Theorem 3.1

import Definitions.Def_DetDLP_M89_S1_Queries
import Definitions.Def_DetDLP_S8C_TagSpec
import Definitions.Def_DetDLP_W1_Queries

set_option autoImplicit false
namespace DetDLP.S8H.ECElem
open M89S1
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

variable {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))

def word {m : ℕ} (T : ℕ) (S : ECSeed p m) (i : Fin m) (η : List Bool) :=
  queryWord 4 (encodeCurveInput p E) [countWord T,List.ofFn (ecBits S),countWord i.val,η]

variable [E.IsElliptic]

noncomputable def value {m : ℕ} (T : ℕ) (S : ECSeed p m) (i : Fin m) (η : List Bool) :=
  elemCount (ecFactorBlock E T S i) (ecWord (bitLen p)) η

/-- The outer tag can be read before inspecting the query's dependent indices. -/
theorem tagIntro (make port : List Bool → List Bool) (L : ℕ) (hm : Groundwork.PolyT make)
    (he : Groundwork.PolyT port)
    (h : ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
      ∀ (T : ℕ) (S : ECSeed p (blockCount (bitLen p))) (i : Fin (blockCount (bitLen p))) (η : List Bool),
      T ≤ p → η.length ≤ 2*bitLen p+1 →
      S8C.Realizes make port L (word E T S i η) (bitLen p) (value E T S i η)) :
    S8C.TagSpec [4] := by
  refine ⟨make,port,L,hm,he,?_⟩
  rintro t ht base payload b n hq
  obtain rfl : t = 4 := by simpa using ht
  generalize hw : queryWord 4 base payload = w at hq ⊢
  have tag : Groundwork.PolyT.bval (DetDLP_W1_Queries.first w) = 4 := by subst w; simp [queryWord]
  cases hq <;> simp only [queryWord,DetDLP_W1_Queries.first_cons,id_eq,DetDLP_W1_Queries.decode_count] at tag
  all_goals first | contradiction | exact h _ (by assumption) _ _ _ _ _ (by assumption) (by assumption)

end DetDLP.S8H.ECElem


