-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
-- name    : Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:21:12.005833+00:00
-- url     : https://prove2.me/theorems/cde328af-6d14-4a35-998b-5a5e8f2157ca
-- title:
--   Deg Prod
-- statement:
--   Definitions and structural lemmas for Deg Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/KeyFormula/DegProd.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KeyKa
def TorsSq {R Ix : Type} [CommRing R] [Fintype Ix] [DecidableEq Ix] (deg : Ix → ℕ) (D : Matrix Ix Ix R) (t : R) : Prop :=
  ∃ h : Matrix Ix Ix R, (∀ p q, deg p ≠ deg q + 1 → h p q = 0) ∧ D * h + h * D = 1 ∧
    ∃ e : {p // Even (deg p)} ≃ {p // ¬ Even (deg p)},
      t = ((D + h).submatrix (fun p : {p // Even (deg p)} => p.1) (fun p => (e p).1)).det ^ 2
def IsCx {R Ix : Type} [CommRing R] [Fintype Ix] (deg : Ix → ℕ) (D : Matrix Ix Ix R) : Prop :=
  (∀ p q, deg q ≠ deg p + 1 → D p q = 0) ∧ D * D = 0
abbrev KIx (g d : ℕ) (N : ℕ → ℕ) : Type := (Σ I : Finset (Fin g), Fin (N I.card)) ⊕ Fin d
def kdeg {g d : ℕ} {N : ℕ → ℕ} : KIx g d N → ℕ
  | .inl p => p.1.card + 1
  | .inr _ => 0
def kosD {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ} (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R)
    (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R) : Matrix (KIx g d N) (KIx g d N) R
  | .inl p, .inl q => ∑ i, if i ∉ p.1 ∧ q.1 = insert i p.1 then
      (-1) ^ (p.1.filter (· < i)).card * m i _ _ p.2 q.2 else 0
  | .inr a, .inl q => if q.1 = ∅ then ev _ a q.2 else 0
  | _, .inr _ => 0
def degProd (g n l l' : ℕ) : ℕ := ∏ j ∈ Finset.range (g + 1), (l - j * n) * (l' - j * n)
def tComb {R : Type} [CommRing R] (g n l Pr : ℕ) (t : Rˣ) (lam : ℕ → Rˣ) : Rˣ :=
  t ^ (4 * Pr ^ (3 * g + 2)) *
    ∏ j ∈ Finset.range (g + 1), lam j ^ ((-1 : ℤ) ^ j * (g.choose j : ℤ) * ((Pr / (l - j * n)) ^ (3 * g + 2) : ℕ))
def kaForm {R : Type} [CommRing R] (g n l l' : ℕ) (t t' : Rˣ) (lam lam' : ℕ → Rˣ) (J : Rˣ) : Rˣ :=
  tComb g n l (degProd g n l l') t lam ^ ((g * n : ℤ) - 2 * l') *
    tComb g n l' (degProd g n l l') t' lam' ^ ((2 * l : ℤ) - g * n) *
    J ^ (8 * (degProd g n l l' ^ (3 * g + 2) : ℕ) * ((l' : ℤ) - l))
def kaExp (g n l l' : ℕ) : ℕ := 2 * degProd g n l l' ^ (3 * g + 2) * (g.factorial * n ^ g) * (l' - l)
end GlobalTheory.KeyKa
end


