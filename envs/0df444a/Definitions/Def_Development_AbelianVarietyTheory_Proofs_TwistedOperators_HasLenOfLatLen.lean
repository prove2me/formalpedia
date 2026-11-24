-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T16:08:49.431642+00:00
-- url     : https://prove2.me/theorems/b9ed7f3e-14a0-4bf6-a2b3-57020ef0d917
-- title:
--   Has Len Of Lat Len
-- statement:
--   Definitions and structural lemmas for Has Len Of Lat Len, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasLenOfLatLen.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix MeasureTheory GlobalTheory.SatakeWeyl
namespace GlobalTheory.InertZeta
section Len
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
def IsInt {ι κ : Type} (M : Matrix ι κ L) : Prop := ∀ i j, M i j ∈ intL L
def IsFrac (g U V C : Matrix (Fin n) (Fin n) L) : Prop :=
  IsInt U ∧ IsInt V ∧ IsInt C ∧ IsInt (g * C) ∧ (U + V * g) * C = 1
def HasLen (g : Matrix (Fin n) (Fin n) L) (k : ℕ) : Prop :=
  ∃ U V C, IsFrac g U V C ∧ Valued.v C.det = WithZero.exp (-(k : ℤ))
def len (g : Matrix (Fin n) (Fin n) L) : ℕ := sInf {k | HasLen g k}
def rowLat {ι : Type} (M : Matrix ι (Fin n) L) : Submodule (intL L) (Fin n → L) :=
  Submodule.span (intL L) (Set.range fun i => M i)
def LatLen (R : Submodule (intL L) (Fin n → L)) (k : ℤ) : Prop :=
  ∃ M : Matrix (Fin n) (Fin n) L, Valued.v M.det = WithZero.exp k ∧ R = rowLat M
def intV (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) : AddSubgroup (Fin n → L) :=
  AddSubgroup.pi Set.univ fun _ => (intL L).toAddSubgroup
def preLat (A : Matrix (Fin n) (Fin n) L) : AddSubgroup (Fin n → L) := (intV L n).comap A.vecMulLinear.toAddMonoidHom
def traceZero (σ : L →+* L) (c : L) : AddSubgroup L :=
  (intL L).toAddSubgroup.comap (AddMonoidHom.mulLeft c) ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker
end Len
section Parabolic
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
def mid (i : Fin N) : Fin (N + 2) := i.castSucc.succ
def blk (N : ℕ) (i : Fin (N + 2)) : ℕ := if i = 0 then 0 else if i = Fin.last (N + 1) then 2 else 1
abbrev radQ (σ : L →+* L) (N : ℕ) : Subgroup (GU σ (N + 2)) := radU σ (blk N)
abbrev RadQuot (σ : L →+* L) (N : ℕ) : Type := radQ σ N ⧸ (KU σ (N + 2)).subgroupOf (radQ σ N)
def rowOf (u : GU σ (N + 2)) : Fin N → L := fun j => mat u 0 (mid j)
def colOf (u : GU σ (N + 2)) : Fin N → L := fun i => mat u (mid i) (Fin.last (N + 1))
def cornerOf (u : GU σ (N + 2)) : L := mat u 0 (Fin.last (N + 1))
def IsLeviElt (ϖ : L) (a : ℤ) (g₀ : GU σ N) (m : GU σ (N + 2)) : Prop :=
  m ∈ leviU σ (blk N) ∧ mat m 0 0 = ϖ ^ a ∧ mat m (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-a) ∧
    ∀ i j, mat m (mid i) (mid j) = mat g₀ i j
def Small (ϖ : L) (e f : ℕ) (C D : Matrix (Fin N) (Fin N) L) (u : GU σ (N + 2)) : Prop :=
  (∀ j, ϖ ^ e * (rowOf u ᵥ* C) j ∈ intL L) ∧ ϖ ^ f * (cornerOf u - rowOf u ⬝ᵥ (D *ᵥ colOf u)) ∈ intL L
end Parabolic
def zVal (q n : ℕ) (X y : ℂ) {m : ℕ} (α : Fin m → ℂ) : ℂ :=
  (∏ j ∈ Finset.range n, (1 - (-(q : ℂ)) ^ j * X)) *
    (∏ i, (1 - y * α i)⁻¹ * (1 - y / α i)⁻¹) * (if Odd n then (1 - y)⁻¹ else 1)
def jFac (q N : ℕ) (X : ℂ) : ℂ := (1 - X) * (1 + q * X) / (1 - ((q : ℂ) ^ (N + 1) * X) ^ 2)
def Smith : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (n : ℕ),
    Valued.v ϖ = WithZero.exp (-1 : ℤ) → ∀ g : Matrix (Fin n) (Fin n) L, g.det ≠ 0 →
    ∃ (d : Fin n → ℤ) (a a' b b' : Matrix (Fin n) (Fin n) L), IsInt a ∧ IsInt a' ∧ IsInt b ∧ IsInt b' ∧
      a' * a = 1 ∧ b * b' = 1 ∧ g = a * Matrix.diagonal (fun i => ϖ ^ d i) * b
def FracExists : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (n : ℕ),
    Valued.v ϖ = WithZero.exp (-1 : ℤ) → ∀ g : Matrix (Fin n) (Fin n) L, g.det ≠ 0 → HasLen g (len g)
def Completion : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ),
    IsUnramInv ϖ σ q → ∀ (g : GU σ n) (U V C : Matrix (Fin n) (Fin n) L), IsFrac (mat g) U V C →
    ∃ k ∈ UJ σ (GlobalTheory.Doubling.dblGram (finSumFinEquiv (m := n) (n := n)) (antiJ L n)), k ∈ GLint (Fin (n + n)) (intL L) ∧
      ∀ x : Fin n → L, (k : Matrix (Fin (n + n)) (Fin (n + n)) L) *ᵥ
      GlobalTheory.Doubling.pairVec finSumFinEquiv x x = GlobalTheory.Doubling.pairVec finSumFinEquiv (C *ᵥ x) ((mat g * C) *ᵥ x)
def AddVec : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) (M : Matrix (Fin n) (Fin n) L) (k : ℤ)
    (ρ : Fin n → L) (e : ℕ), Valued.v M.det = WithZero.exp k → (∀ i, Valued.v (ρ i) ≤ WithZero.exp (e : ℤ)) →
    (e = 0 ∨ ∃ i, Valued.v (ρ i) = WithZero.exp (e : ℤ)) →
    LatLen (rowLat M ⊔ Submodule.span (intL L) {ρ ᵥ* M}) (k + e)
def Dual : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q N : ℕ),
    IsUnramInv ϖ σ q → ∀ (g : GU σ N) (U V C : Matrix (Fin N) (Fin N) L), IsFrac (mat g) U V C →
    ∀ (r b : Fin N → L) (t : L), (∀ j, r j = -σ (b j.rev)) →
    ((∀ j, t * (r ᵥ* C) j ∈ intL L) ↔
      (∀ i, t * ((C * V * mat g) *ᵥ b) i ∈ intL L) ∧ ∀ i, t * ((mat g * C * U) *ᵥ b) i ∈ intL L)
def SpanEq : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (N : ℕ) (a : ℤ)
    (g : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (g₀ U V C : Matrix (Fin N) (Fin N) L) (r b : Fin N → L) (c y : L),
    Valued.v ϖ = WithZero.exp (-1 : ℤ) → IsFrac g₀ U V C →
    g 0 0 = ϖ ^ a → (∀ j, g 0 (mid j) = ϖ ^ a * r j) → g 0 (Fin.last (N + 1)) = ϖ ^ a * c →
    (∀ i, g (mid i) 0 = 0) → (∀ i j, g (mid i) (mid j) = g₀ i j) → (∀ i, g (mid i) (Fin.last (N + 1)) = (g₀ *ᵥ b) i) →
    g (Fin.last (N + 1)) 0 = 0 → (∀ j, g (Fin.last (N + 1)) (mid j) = 0) →
    g (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-a) →
    WithZero.exp (a.toNat : ℤ) ≤ Valued.v y → (∀ i, Valued.v (((C * V * g₀) *ᵥ b) i) ≤ Valued.v y) →
    (∀ i, Valued.v (((g₀ * C * U) *ᵥ b) i) ≤ Valued.v y) →
    (Valued.v y = WithZero.exp (a.toNat : ℤ) ∨ (∃ i, Valued.v y = Valued.v (((C * V * g₀) *ᵥ b) i)) ∨
      ∃ i, Valued.v y = Valued.v (((g₀ * C * U) *ᵥ b) i)) →
    ∃ (P : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (ρ : Fin (N + 2) → L),
      Valued.v P.det = WithZero.exp ((-a).toNat : ℤ) * (Valued.v C.det)⁻¹ * Valued.v y ∧ ρ 0 = 0 ∧
      (∀ j, ρ (mid j) = ϖ ^ a.toNat * (r ᵥ* C) j) ∧
      ρ (Fin.last (N + 1)) = ϖ ^ a.toNat * (c - r ⬝ᵥ ((C * V * g₀) *ᵥ b)) / y ∧
      rowLat (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) ⊔ rowLat g = rowLat P ⊔ Submodule.span (intL L) {ρ ᵥ* P}
def Heis : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q N : ℕ),
    IsUnramInv ϖ σ q →
    (∀ u ∈ radQ σ N, (∀ j, rowOf u j = -σ (colOf u j.rev)) ∧
      cornerOf u + σ (cornerOf u) = rowOf u ⬝ᵥ colOf u ∧
      (u ∈ KU σ (N + 2) ↔ (∀ j, rowOf u j ∈ intL L) ∧ cornerOf u ∈ intL L)) ∧
    (∀ u ∈ radQ σ N, ∀ u' ∈ radQ σ N, rowOf (u * u') = rowOf u + rowOf u' ∧ colOf (u * u') = colOf u + colOf u' ∧
      cornerOf (u * u') = cornerOf u + cornerOf u' + rowOf u ⬝ᵥ colOf u') ∧
    ∀ (r : Fin N → L) (c : L), c + σ c = -∑ j, r j * σ (r j.rev) → ∃ u ∈ radQ σ N, rowOf u = r ∧ cornerOf u = c
def Pointwise : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q N : ℕ),
    IsUnramInv ϖ σ q → ∀ (a : ℤ) (g₀ : GU σ N) (m : GU σ (N + 2)), IsLeviElt ϖ a g₀ m →
    ∀ (U V C : Matrix (Fin N) (Fin N) L) (l : ℕ), IsFrac (mat g₀) U V C → Valued.v C.det = WithZero.exp (-(l : ℤ)) →
    ∀ u ∈ radQ σ N, a.natAbs + l ≤ len (mat (m * u)) ∧
      ∀ j : ℕ, len (mat (m * u)) ≤ a.natAbs + l + j ↔ Small ϖ (a.toNat + j / 2) (2 * a.toNat + j) C (C * V * mat g₀) u
def LatIndex : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ),
    IsUnramInv ϖ σ q → ∀ (A : Matrix (Fin n) (Fin n) L) (k : ℕ), IsInt A → Valued.v A.det = WithZero.exp (-(k : ℤ)) →
    (intV L n).relIndex (preLat A) = q ^ (2 * k)
def TraceIndex : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q f : ℕ),
    IsUnramInv ϖ σ q → (traceZero σ 1).relIndex (traceZero σ (ϖ ^ f)) = q ^ f
def SmallCorner : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q N : ℕ),
    IsUnramInv ϖ σ q → ∀ (g₀ : GU σ N) (U V C : Matrix (Fin N) (Fin N) L), IsFrac (mat g₀) U V C →
    ∀ (e f : ℕ) (r : Fin N → L), 2 * e ≤ f → (∀ j, ϖ ^ e * (r ᵥ* C) j ∈ intL L) →
    ∃ u ∈ radQ σ N, rowOf u = r ∧ Small ϖ e f C (C * V * mat g₀) u
def Count : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q N : ℕ),
    IsUnramInv ϖ σ q → ∀ (C D : Matrix (Fin N) (Fin N) L) (l e f : ℕ), IsInt C →
    Valued.v C.det = WithZero.exp (-(l : ℤ)) →
    (∀ r : Fin N → L, (∀ j, ϖ ^ e * (r ᵥ* C) j ∈ intL L) → ∃ u ∈ radQ σ N, rowOf u = r ∧ Small ϖ e f C D u) →
    (∀ u ∈ radQ σ N, ∀ k ∈ radQ σ N, k ∈ KU σ (N + 2) → Small ϖ e f C D u → Small ϖ e f C D (u * k)) →
    Nat.card {x : RadQuot σ N // Small ϖ e f C D (x.out : radQ σ N).1} = q ^ (2 * (l + N * e) + f)
def LeviExists : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q N : ℕ),
    IsUnramInv ϖ σ q → ∀ (a : ℤ) (g₀ : GU σ N), ∃ m : GU σ (N + 2), IsLeviElt ϖ a g₀ m
def CosetSurj : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q N : ℕ),
    IsUnramInv ϖ σ q → ∀ g : GU σ (N + 2), ∃ (a : ℤ) (y : GU σ N ⧸ KU σ N), ∀ m, IsLeviElt ϖ a y.out m →
      ∃ u ∈ radQ σ N, ∃ k ∈ KU σ (N + 2), g = m * u * k
def CosetInj : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q N : ℕ),
    IsUnramInv ϖ σ q → ∀ (a a' : ℤ) (g₀ g₀' : GU σ N) (m m' : GU σ (N + 2)), IsLeviElt ϖ a g₀ m → IsLeviElt ϖ a' g₀' m' →
      ∀ u ∈ radQ σ N, ∀ u' ∈ radQ σ N, (m * u)⁻¹ * (m' * u') ∈ KU σ (N + 2) → a = a' ∧ g₀⁻¹ * g₀' ∈ KU σ N
def SphTrans : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q N r : ℕ),
    IsUnramInv ϖ σ q → 2 * r ≤ N → ∀ (α : Fin (r + 1) → ℂ) (φ : GU σ (N + 2) → ℂ) (φ₀ : GU σ N → ℂ), (∀ i, α i ≠ 0) →
    IsSphericalU q α φ → φ 1 = 1 → IsSphericalU q (Fin.tail α) φ₀ → φ₀ 1 = 1 →
    ∀ (a : ℤ) (g₀ : GU σ N) (m : GU σ (N + 2)), IsLeviElt ϖ a g₀ m → ∀ u ∈ radQ σ N,
      φ (m * u) = α 0 ^ a * (q : ℂ) ^ (-a * ((N : ℤ) + 1)) * φ₀ g₀
def SmallRank : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ),
    IsUnramInv ϖ σ q → n ≤ 1 → ∀ g : GU σ n, g ∈ KU σ n
def CosetIntegral : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G), IsOpen (K : Set G) → μ K = 1 →
    ∀ (F : G → ℂ) (Z : ℂ), (∀ g, ∀ k ∈ K, F (g * k) = F g) → HasSum (fun x : G ⧸ K => F x.out) Z →
    Integrable F μ ∧ ∫ g, F g ∂μ = Z
def DosetSwap : Prop :=
  ∀ (G : Type) [Group G] (K : Subgroup G), IsCommensurated K → ∀ (F w φ : G → ℂ) (Z : ℂ), IsBiInv K F → IsBiInv K w →
    (∀ g, hAct K (dosetInd ℂ K g) w 1 = hAct K (dosetInd ℂ K g) φ 1) →
    HasSum (fun x : G ⧸ K => F x.out * φ x.out) Z → HasSum (fun x : G ⧸ K => F x.out * w x.out) Z
def GenFun : Prop :=
  ∀ (ι : Type) (f : ι → ℕ) (l c q N : ℕ) (X : ℂ), 1 ≤ c → 1 ≤ q → (∀ i, l ≤ f i) →
    (∀ j : ℕ, Nat.card {i // f i ≤ l + j} = c * q ^ (2 * N * (j / 2) + j)) → ‖(q : ℂ) ^ (N + 1) * X‖ < 1 →
    HasSum (fun i => X ^ f i) (c * X ^ l * jFac q N X)
def Step : Prop :=
  ∀ (Y C : Type) (q N : ℕ) (ℓ : ℤ → Y → C → ℕ) (l : Y → ℕ) (φ₀ : Y → ℂ) (α X y Z : ℂ), 1 ≤ q → α ≠ 0 →
    y = (q : ℂ) ^ (N + 1) * X → ‖y‖ < 1 → ‖y‖ * ‖α‖ < 1 → ‖y‖ * ‖α‖⁻¹ < 1 →
    (∀ X' : ℂ, ‖(q : ℂ) ^ (N + 1) * X'‖ < 1 → ∀ a b, HasSum (fun c => X' ^ ℓ a b c)
      ((q : ℂ) ^ (2 * l b + (2 * N + 2) * a.toNat) * X' ^ (a.natAbs + l b) * jFac q N X')) →
    HasSum (fun b => ((q : ℂ) ^ 2 * X) ^ l b * φ₀ b) Z →
    HasSum (fun p : (ℤ × Y) × C => X ^ ℓ p.1.1 p.1.2 p.2 * (α ^ p.1.1 * (q : ℂ) ^ (-p.1.1 * ((N : ℤ) + 1)) * φ₀ p.1.2))
      ((1 - X) * (1 + q * X) * ((1 - y * α)⁻¹ * (1 - y / α)⁻¹) * Z)
end GlobalTheory.InertZeta
end


