-- Prove2me | Definitions.Def_DerivativeChainPrivate_hermite_closed
-- name    : DerivativeChainPrivate_hermite_closed
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-18T08:18:33.469248+00:00
-- url     : https://prove2.me/theorems/b97c90b8-0ecf-4bdc-a91a-21ac1cfb61db
-- title:
--   Finite Hermite tower, complete closed chains, and uniform root variance
-- statement:
--   Defines the explicit Hermite polynomials through degree six, complete real-root chains, their cost plus return to zero, the infimum over all such chains, and the uniform variance computed from the full root multiset and its mean. Degree-five chains ignore the last slot of a six-slot vector. The model also includes an explicit degree-five witness used by the proof.
-- source:
--   Derivative-zero chains: public formalization reference, R03, DerivativeChainPrivate_hermite_closed. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1600000
open Polynomial
namespace DerivativeChainPrivate.Hermite

noncomputable def H (m : ℕ) : Polynomial ℝ :=
  match m with
  | 1 => X
  | 2 => X^2 - 1
  | 3 => X^3 - 3*X
  | 4 => X^4 - 6*X^2 + 3
  | 5 => X^5 - 10*X^3 + 15*X
  | 6 => X^6 - 15*X^4 + 45*X^2 - 15
  | _ => 1

noncomputable def cost (z : Fin 6 → ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (m-1), |z ⟨min (i+1) 5, by omega⟩ - z ⟨min i 5, by omega⟩|











end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite



noncomputable def ClosedCost (z : Fin 6 → ℝ) (m : ℕ) : ℝ :=
  cost z m + |z ⟨min (m-1) 5, by omega⟩|

def Chain (m : ℕ) (z : Fin 6 → ℝ) : Prop :=
  ∀ i : Fin 6, i.val < m → (H (i.val+1)).eval (z i) = 0



end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite





noncomputable def witness5 : Fin 6 → ℝ :=
  ![0, 1, Real.sqrt 3, Real.sqrt (3-Real.sqrt 6), 0, 0]





noncomputable def Budget (m : ℕ) : ℝ :=
  sInf {c : ℝ | ∃ z : Fin 6 → ℝ, Chain m z ∧ c = ClosedCost z m}











end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite





noncomputable def Variance (m : ℕ) : ℝ :=
  -2*(H m).coeff (m-2)/(m : ℝ)





end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite









noncomputable def UniformVariance (m : ℕ) : ℝ :=
  (((H m).roots.map (fun x => (x - (H m).roots.sum / (m:ℝ))^2)).sum) / (m:ℝ)



end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite





end DerivativeChainPrivate.Hermite


