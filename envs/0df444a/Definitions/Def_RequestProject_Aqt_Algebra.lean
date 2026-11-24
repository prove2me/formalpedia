-- Prove2me | Definitions.Def_RequestProject_Aqt_Algebra
-- name    : RequestProject_Aqt_Algebra
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T22:49:05.86088+00:00
-- url     : https://prove2.me/theorems/6868c780-868b-4b72-8a48-02445a13e352
-- title:
--   Algebra
-- statement:
--   Definitions and structural lemmas for Algebra, from SashaIr/leaving-the-hall contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Dyck-path algebra and decorated-Dyck-path bijection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Algebra.lean

import Mathlib
set_option autoImplicit true
namespace DyckAlgebra
open scoped BigOperators
inductive Gen where
  | eps (k : ℕ)
  | T (k i : ℕ)
  | Tinv (k i : ℕ)
  | dp (k : ℕ)
  | dm (k : ℕ)
  | dps (k : ℕ)
  deriving DecidableEq
variable (𝕜 : Type*) [Field 𝕜]
abbrev Pre : Type _ := FreeAlgebra 𝕜 Gen
namespace Pre
def eps (k : ℕ) : Pre 𝕜 := FreeAlgebra.ι 𝕜 (.eps k)
def T (k i : ℕ) : Pre 𝕜 := FreeAlgebra.ι 𝕜 (.T k i)
def Tinv (k i : ℕ) : Pre 𝕜 := FreeAlgebra.ι 𝕜 (.Tinv k i)
def dp (k : ℕ) : Pre 𝕜 := FreeAlgebra.ι 𝕜 (.dp k)
def dm (k : ℕ) : Pre 𝕜 := FreeAlgebra.ι 𝕜 (.dm k)
def dps (k : ℕ) : Pre 𝕜 := FreeAlgebra.ι 𝕜 (.dps k)
def Tdown (k : ℕ) : ℕ → Pre 𝕜
  | 0 => 1
  | n + 1 => T 𝕜 k (n + 1) * Tdown k n
def TdownStar (k : ℕ) : ℕ → Pre 𝕜
  | 0 => 1
  | n + 1 => Tinv 𝕜 k (n + 1) * TdownStar k n
def comm (k : ℕ) : Pre 𝕜 :=
  if k = 0 then -(dm 𝕜 0 * dp 𝕜 0)
  else dp 𝕜 (k - 1) * dm 𝕜 (k - 1) - dm 𝕜 k * dp 𝕜 k
def commStar (k : ℕ) : Pre 𝕜 :=
  if k = 0 then -(dm 𝕜 0 * dps 𝕜 0)
  else dps 𝕜 (k - 1) * dm 𝕜 (k - 1) - dm 𝕜 k * dps 𝕜 k
def yy (q : 𝕜) (k : ℕ) : ℕ → Pre 𝕜
  | 0 => 0
  | 1 => (q ^ (k - 1) * (q - 1))⁻¹ • (comm 𝕜 k * Tdown 𝕜 k (k - 1))
  | i + 2 => q • (Tinv 𝕜 k (i + 1) * yy q k (i + 1) * Tinv 𝕜 k (i + 1))
def zz (q t : 𝕜) (k : ℕ) : ℕ → Pre 𝕜
  | 0 => 0
  | 1 => ((q * t)⁻¹ * (q ^ k * (1 - q)⁻¹)) •
      (commStar 𝕜 k * TdownStar 𝕜 k (k - 1))
  | i + 2 => q⁻¹ • (T 𝕜 k (i + 1) * zz q t k (i + 1) * T 𝕜 k (i + 1))
end Pre
open Pre
variable {𝕜}
inductive Rel (q t : 𝕜) : Pre 𝕜 → Pre 𝕜 → Prop
  -- vertex/path support
  | eps_idem (k) : Rel q t (eps 𝕜 k * eps 𝕜 k) (eps 𝕜 k)
  | eps_orth (k l) (h : k ≠ l) : Rel q t (eps 𝕜 k * eps 𝕜 l) 0
  | T_support (k i) : Rel q t (eps 𝕜 k * T 𝕜 k i * eps 𝕜 k) (T 𝕜 k i)
  | Tinv_support (k i) : Rel q t (eps 𝕜 k * Tinv 𝕜 k i * eps 𝕜 k) (Tinv 𝕜 k i)
  | dp_support (k) : Rel q t (eps 𝕜 (k+1) * dp 𝕜 k * eps 𝕜 k) (dp 𝕜 k)
  | dm_support (k) : Rel q t (eps 𝕜 k * dm 𝕜 k * eps 𝕜 (k+1)) (dm 𝕜 k)
  | dps_support (k) : Rel q t (eps 𝕜 (k+1) * dps 𝕜 k * eps 𝕜 k) (dps 𝕜 k)
  -- Hecke relations
  | skein (k i) (hi : 1 ≤ i ∧ i < k) :
      Rel q t ((T 𝕜 k i - eps 𝕜 k) * (T 𝕜 k i + q • eps 𝕜 k)) 0
  | braid (k i) (hi : 1 ≤ i ∧ i + 1 < k) :
      Rel q t (T 𝕜 k i * T 𝕜 k (i+1) * T 𝕜 k i)
        (T 𝕜 k (i+1) * T 𝕜 k i * T 𝕜 k (i+1))
  | Tcomm (k i j) (h : 1 ≤ i ∧ i + 1 < j ∧ j < k) :
      Rel q t (T 𝕜 k i * T 𝕜 k j) (T 𝕜 k j * T 𝕜 k i)
  | TinvL (k i) (hi : 1 ≤ i ∧ i < k) : Rel q t (T 𝕜 k i * Tinv 𝕜 k i) (eps 𝕜 k)
  | TinvR (k i) (hi : 1 ≤ i ∧ i < k) : Rel q t (Tinv 𝕜 k i * T 𝕜 k i) (eps 𝕜 k)
  -- A_q: R1--R6
  | R1 (k i) (h : 2 ≤ i ∧ i ≤ k - 2) :
      Rel q t (dm 𝕜 (k-1) * T 𝕜 k i) (T 𝕜 (k-1) i * dm 𝕜 (k-1))
  | R2 (k i) (h : 1 ≤ i ∧ i < k) :
      Rel q t (dp 𝕜 k * T 𝕜 k i) (T 𝕜 (k+1) (i+1) * dp 𝕜 k)
  | R3 (k) : Rel q t (T 𝕜 (k+2) 1 * dp 𝕜 (k+1) * dp 𝕜 k) (dp 𝕜 (k+1) * dp 𝕜 k)
  | R4 (k) (hk : 2 ≤ k) :
      Rel q t (dm 𝕜 (k-2) * dm 𝕜 (k-1) * T 𝕜 k (k-1)) (dm 𝕜 (k-2) * dm 𝕜 (k-1))
  | R5 (k) (hk : 2 ≤ k) :
      Rel q t (dm 𝕜 (k-1) * comm 𝕜 k * T 𝕜 k (k-1))
        (q • (comm 𝕜 (k-1) * dm 𝕜 (k-1)))
  | R6 (k) : Rel q t (T 𝕜 (k+1) 1 * comm 𝕜 (k+1) * dp 𝕜 k)
      (q • (dp 𝕜 k * comm 𝕜 k))
  -- A_{q⁻¹}: starred R1--R6
  | R1s (k i) (h : 2 ≤ i ∧ i ≤ k - 2) :
      Rel q t (dm 𝕜 (k-1) * Tinv 𝕜 k i) (Tinv 𝕜 (k-1) i * dm 𝕜 (k-1))
  | R2s (k i) (h : 1 ≤ i ∧ i < k) :
      Rel q t (dps 𝕜 k * Tinv 𝕜 k i) (Tinv 𝕜 (k+1) (i+1) * dps 𝕜 k)
  | R3s (k) : Rel q t (Tinv 𝕜 (k+2) 1 * dps 𝕜 (k+1) * dps 𝕜 k) (dps 𝕜 (k+1) * dps 𝕜 k)
  | R4s (k) (hk : 2 ≤ k) :
      Rel q t (dm 𝕜 (k-2) * dm 𝕜 (k-1) * Tinv 𝕜 k (k-1)) (dm 𝕜 (k-2) * dm 𝕜 (k-1))
  | R5s (k) (hk : 2 ≤ k) :
      Rel q t (dm 𝕜 (k-1) * commStar 𝕜 k * Tinv 𝕜 k (k-1))
        (q⁻¹ • (commStar 𝕜 (k-1) * dm 𝕜 (k-1)))
  | R6s (k) : Rel q t (Tinv 𝕜 (k+1) 1 * commStar 𝕜 (k+1) * dps 𝕜 k)
      (q⁻¹ • (dps 𝕜 k * commStar 𝕜 k))
  -- gluing relations of A_{q,t}; yy and zz are the derived words above
  | Q1 (k i) (hi : 1 ≤ i ∧ i ≤ k) :
      Rel q t (zz 𝕜 q t (k+1) (i+1) * dp 𝕜 k) (dp 𝕜 k * zz 𝕜 q t k i)
  | Q1s (k i) (hi : 1 ≤ i ∧ i ≤ k) :
      Rel q t (yy 𝕜 q (k+1) (i+1) * dps 𝕜 k) (dps 𝕜 k * yy 𝕜 q k i)
  | Q2 (k) : Rel q t (zz 𝕜 q t (k+1) 1 * dp 𝕜 k)
      ((-(q ^ k)) • (yy 𝕜 q (k+1) 1 * dps 𝕜 k))
abbrev Aqt (q t : 𝕜) : Type _ := RingQuot (Rel q t)
end DyckAlgebra


