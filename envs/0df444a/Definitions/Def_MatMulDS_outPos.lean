-- Prove2me | Definitions.Def_MatMulDS_outPos
-- name    : MatMulDS_outPos
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:05:13.507283+00:00
-- url     : https://prove2.me/theorems/0b60d339-f42f-4c1d-8ba9-b1c04505f8f2
-- title:
--   Types, default sets and the identity with $5^4$ products
-- statement:
--   The outputs of the identity $T_5^{(4)}$ with $5^4$ products are strings $w=(w_1,w_2,w_3,w_4)$ of outputs of the five-term identity, and its products are strings $R=(R_1,R_2,R_3,R_4)$ of products. The **type** $\tau(w)\subseteq[4]$ is the set of positions with $w_\ell=z_0$, and the **default set** $S(R)$ is the set of positions with $R_\ell=P_0$. The private map sends $w$ to the string of private products of its entries.
--
--   An output of type $\tau$ has length
--   $$d_\tau=\begin{cases}184,&\tau=[4],\\2^{|\tau|+1},&\tau\ne[4]\text{ contains }\{1,2\}\text{ or }\{3,4\},\\2^{|\tau|},&\text{otherwise.}\end{cases}$$
--   A distribution $p$ on types gives the distribution $\pi$ on outputs with $\pi(w)=p_\tau/4^{4-|\tau|}$. The predicate `IsTFour` says that an identity is obtained from the five-term identity by squaring and enlarging twice.
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), §7.1, pp.44–45 (PDF pp.46–47)

import Mathlib
import Definitions.Def_MatMulDS_fiveTensor
import Definitions.Def_MatMulDS_IsEnlargement

set_option autoImplicit false

namespace MatMulDS

/-- The index type of the outputs of the fourth tensor power of the five-term tensor, with rows and columns
split as in the iterated tensor square. -/
abbrev O4 : Type := ((Fin 3 × Fin 3) × (Fin 3 × Fin 3)) × ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))

/-- The strings `R = (R1, R2, R3, R4)` of four products of the five-term identity (§7.1, p.44). -/
abbrev P4 : Type := (Fin 5 × Fin 5) × (Fin 5 × Fin 5)

/-- The entry `w_ℓ` of an output `w = (w1, w2, w3, w4)` (§7.1, p.44); 0-based `ℓ`. -/
def outPos (o : O4) : Fin 4 → Fin 3 × Fin 2 :=
  ![(o.1.1.1, o.2.1.1), (o.1.1.2, o.2.1.2), (o.1.2.1, o.2.2.1), (o.1.2.2, o.2.2.2)]

/-- The entry `R_ℓ` of a product `R = (R1, R2, R3, R4)` (§7.1, p.44). -/
def prodPos (R : P4) : Fin 4 → Fin 5 := ![R.1.1, R.1.2, R.2.1, R.2.2]

/-- The **type** `τ(w) ⊆ [4]`: the positions with `w_ℓ = z0` (§7.1, p.44). -/
def typeOf (o : O4) : Finset (Fin 4) := Finset.univ.filter fun ℓ => outPos o ℓ = (2, 0)

/-- The **default set** `S(R) ⊆ [4]`: the positions with `R_ℓ = P0` (§7.1, p.44). -/
def defaultSet (R : P4) : Finset (Fin 4) := Finset.univ.filter fun ℓ => prodPos R ℓ = 4

/-- The private map of §7.1, p.44: `w` goes to the product with `P0` at the positions of `τ(w)` and `P_ij` at the
positions with `w_ℓ = z_ij`. -/
def privFour (o : O4) : P4 :=
  ((fivePrivateFn (outPos o 0), fivePrivateFn (outPos o 1)),
   (fivePrivateFn (outPos o 2), fivePrivateFn (outPos o 3)))

/-- The length `d_τ` of an output of type `τ`, (7.1), p.44: `2^{|τ|+1}` if `τ ≠ [4]` contains `{1,2}` or `{3,4}`,
`2^{|τ|}` if `τ` contains neither, and `184` if `τ = [4]`. -/
def lenOfType (τ : Finset (Fin 4)) : ℕ :=
  if τ = Finset.univ then 184
  else if {0, 1} ⊆ τ ∨ {2, 3} ⊆ τ then 2 ^ (τ.card + 1)
  else 2 ^ τ.card

/-- The distribution of Proposition 7.1, p.45: every output of type `τ` has probability `p_τ / 4^{4−|τ|}`. -/
def piFour (p : Finset (Fin 4) → ℚ) (o : O4) : ℚ :=
  p (typeOf o) / 4 ^ (4 - (typeOf o).card)

/-- The identity `T5^(4)` of §7.1, p.44, by its construction: the five-term identity squared and enlarged, then
squared and enlarged again. -/
structure IsTFour {n₁ n₂ : ℕ}
    (T₁ : BlockTensor (Fin 3 × Fin 3) ((Fin 2 × Fin 2) ⊕ Fin n₁) (Fin 2 × Fin 2) (Fin 2 × Fin 2))
    (D₁ : IdentityData (Fin 3 × Fin 3) ((Fin 2 × Fin 2) ⊕ Fin n₁) (Fin 2 × Fin 2) (Fin 5 × Fin 5))
    (T₂ : BlockTensor ((Fin 3 × Fin 3) × (Fin 3 × Fin 3))
      ((((Fin 2 × Fin 2) ⊕ Fin n₁) × ((Fin 2 × Fin 2) ⊕ Fin n₁)) ⊕ Fin n₂)
      ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)))
    (D₂ : IdentityData ((Fin 3 × Fin 3) × (Fin 3 × Fin 3))
      (((((Fin 2 × Fin 2) ⊕ Fin n₁) × ((Fin 2 × Fin 2) ⊕ Fin n₁))) ⊕ Fin n₂)
      ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) P4) : Prop where
  step₁ : IsEnlargement fiveTensor.square fiveData.square (1, 1) (BlockTensor.squareOut (2, 0)) T₁ D₁
  step₂ : IsEnlargement T₁.square D₁.square ((1, 1), (1, 1))
    (BlockTensor.squareOut (BlockTensor.squareOut ((2 : Fin 3), (0 : Fin 2)))) T₂ D₂

end MatMulDS


