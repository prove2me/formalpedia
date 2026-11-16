-- Prove2me | Definitions.Def_FluidGreedyMatching_CliqueBomb_Supplement_PawPool
-- name    : FluidGreedyMatching_CliqueBomb_Supplement_PawPool
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:13:18.494499+00:00
-- url     : https://prove2.me/theorems/b5f8b6c9-53d9-4eeb-86f6-e33c3cf892e1
-- title:
--   The paw with a pool and its common preference order
-- statement:
--   For real $\beta>0$ and an integer size $n\ge1$, take vertices $a_i,b_i,c_i,d_i$ for $i<n$ and $e_j,f_j$ for $j<\lfloor\beta n\rfloor$. Include exactly the following edges: $a_ib_i,b_ic_i,c_ia_i,c_id_i$ inside each paw; $e_jf_j$ inside each pool pair; all distinct pairs within $E=\{e_j\}$; and all pairs $d_ie_j$. This is a finite simple graph $PP_n(\beta)$; the formula $\nu(PP_n(\beta))=2n+\lfloor\beta n\rfloor$ is a mathematical fact and is not used to define its matching number.
--
--   Every actor uses the same total order
--   $$E\succ C\succ B\succ A\succ F\succ D,$$
--   with lower indices preferred within a class. Define $r_{\rm paw}(\beta,j)$ to be its RDO expected matching size divided by its actual maximum matching number at size $n=j+1$.
--
--   This provides the source construction for Proposition 4.3 and the existential examples in Theorem 1.5. The order's helper proof establishes only injectivity of class/index labels. Floor counts permit an empty pool at small sizes without restricting the parameter or the sequence.
-- source:
--   Sayan Mukherjee, Fluid Limits and Upper Bounds for Randomized Greedy Matching, STOC 2027 submission #492 (October 2026), §4.4, pp. 17–18; Fig. 1.1(d), p. 3

import Mathlib
import Definitions.Def_FluidGreedyMatching_CliqueBomb_Supplement_RDOModel

set_option autoImplicit false

namespace FluidGreedyMatching.CliqueBomb.Supplement

noncomputable section

/-- Four paw positions A,B,C,D and two pool positions E,F. -/
abbrev PawVertex (n m : ℕ) := (Fin 4 × Fin n) ⊕ (Fin 2 × Fin m)

def poolSize (β : ℝ) (n : ℕ) : ℕ := ⌊β * (n : ℝ)⌋₊

/-- Directed edge generators, symmetrized below. Only in-copy paw and pool edges
are sparse; E is a clique and D--E is a complete join. -/
def pawEdge {n m : ℕ} : PawVertex n m → PawVertex n m → Prop
  | .inl (c, i), .inl (d, j) => i = j ∧
      ((c = 0 ∧ d = 1) ∨ (c = 1 ∧ d = 2) ∨
       (c = 2 ∧ d = 0) ∨ (c = 2 ∧ d = 3))
  | .inl (c, _), .inr (d, _) => c = 3 ∧ d = 0
  | .inr (c, i), .inr (d, j) =>
      (c = 0 ∧ d = 1 ∧ i = j) ∨ (c = 0 ∧ d = 0)
  | .inr _, .inl _ => False

/-- §4.4, p. 18: the actual graph, without assuming its matching number. -/
def pawPool (β : ℝ) (n : ℕ) : SimpleGraph (PawVertex n (poolSize β n)) where
  Adj v w := v ≠ w ∧ (pawEdge v w ∨ pawEdge w v)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Tags 0=A,1=B,2=C,3=D,4=E,5=F. -/
def pawCode {n m : ℕ} : PawVertex n m → ℕ × ℕ
  | .inl (c, i) => (c.val, i.val)
  | .inr (c, i) => (4 + c.val, i.val)

theorem pawCode_injective {n m : ℕ} : Function.Injective (@pawCode n m) := by
  intro v w h
  cases v with
  | inl v =>
    cases w with
    | inl w => simpa [pawCode, Prod.ext_iff, Fin.ext_iff] using h
    | inr w => have hc := congrArg Prod.fst h; simp [pawCode] at hc; omega
  | inr v =>
    cases w with
    | inl w => have hc := congrArg Prod.fst h; simp [pawCode] at hc; omega
    | inr w => simpa [pawCode, Prod.ext_iff, Fin.ext_iff] using h

/-- The common order E > C > B > A > F > D, lower index preferred. -/
def pawTier (c : ℕ) : ℕ :=
  if c = 4 then 0 else if c = 2 then 1 else if c = 1 then 2
  else if c = 0 then 3 else if c = 5 then 4 else 5

@[instance_reducible] def pawCommonOrder {n m : ℕ} : LinearOrder (PawVertex n m) :=
  orderByTier pawCode pawCode_injective pawTier

@[instance_reducible] def pawProfile {n m : ℕ} (_v : PawVertex n m) : LinearOrder (PawVertex n m) :=
  pawCommonOrder

def pawRatio (β : ℝ) (j : ℕ) : ℝ :=
  rdoExpectedRatio (pawPool β (j + 1)) pawProfile

end
end FluidGreedyMatching.CliqueBomb.Supplement


