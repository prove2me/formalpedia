-- Prove2me | solution 1 for Autoconvolutions.Blocks.coeff_eq_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:55:47.651631+00:00
-- url     : https://prove2.me/submissions/d2dd5f78-e4ca-447f-843e-c40f766b9c1e

module
public import Definitions.Def_Autoconvolutions_BlockExpansion
public import Definitions.Def_Autoconvolutions_Occupancy
public import Definitions.Def_Autoconvolutions_Estimate
public import Definitions.Def_Autoconvolutions_Flat
public import Definitions.Def_Autoconvolutions_Coefficients
public import Theorems.Thm_Autoconvolutions_Blocks_eval_gen_one
public import Theorems.Thm_Autoconvolutions_Blocks_expand_level
public import Theorems.Thm_Autoconvolutions_Blocks_goodVectors_spec
public import Theorems.Thm_Autoconvolutions_Blocks_mem_rows
public import Theorems.Thm_Autoconvolutions_Blocks_rowKey_determines_level
public import Theorems.Thm_Autoconvolutions_Construction_card_evenAlphabet
public import Theorems.Thm_Autoconvolutions_Construction_card_oddAlphabet
public import Theorems.Thm_Autoconvolutions_Construction_family_sq
public import Theorems.Thm_Autoconvolutions_Digits_multinomial_of_distinct
public import Theorems.Thm_Autoconvolutions_Flat_B_coeff_zero
public import Theorems.Thm_Autoconvolutions_Flat_B_flat
attribute [local simp] Autoconvolutions.Blocks.eval_gen_one
attribute [local simp] Autoconvolutions.Construction.card_evenAlphabet
attribute [local simp] Autoconvolutions.Construction.card_oddAlphabet


section
@[expose] public section
open Finset Polynomial
open scoped BigOperators
namespace Autoconvolutions.Blocks
private theorem mem_tickets {m n K D : ℕ} {I J : Finset (Fin m)} {t : Ticket m} :
    t ∈ tickets I J n K D ↔ t.1 ≤ 2*K ∧ t.2 ∈ rows I J (2*n-t.1) (2*n+t.1) D := by
  simp only [tickets, mem_sigma, mem_range, Nat.lt_succ_iff]
private theorem square_expansion {m n K D : ℕ} (I J : Finset (Fin m))
    (hK : K < n) (hD : 4*n < D) :
    (Construction.family Flat.P (gen D I) (gen D J) n K)^2 =
    ∑ t ∈ tickets I J n K D, monomial (rowKey D t.2) (weight I J K t) := by
  classical
  rw [Construction.family_sq _ _ _ hK.le, tickets, Finset.sum_sigma]
  apply sum_congr rfl
  intro s hs
  change (gen D I)^(2*n-s) * (gen D J)^(2*n+s) * Flat.B K s = _
  apply expand_level
  intro h hh
  have hs' := mem_range.mp hs
  exact Flat.B_coeff_zero (by omega)
private theorem ticket_injective {m n K D : ℕ} {I J : Finset (Fin m)}
    (hd : Disjoint I J) (hK : K < n) (hD : 4*n < D)
    {t t' : Ticket m} (ht : t ∈ tickets I J n K D) (ht' : t' ∈ tickets I J n K D)
    (he : rowKey D t.2 = rowKey D t'.2) : t = t' := by
  obtain ⟨s,r⟩ := t
  obtain ⟨s',r'⟩ := t'
  obtain ⟨hs,hr⟩ := mem_tickets.mp ht
  obtain ⟨hs',hr'⟩ := mem_tickets.mp ht'
  dsimp at hs hs' hr hr' he
  obtain ⟨h₁,h₂⟩ := rowKey_determines_level (by omega) hd (by omega) (by omega) hD hr hr' he
  subst s'
  subst r'
  rfl
private theorem coeff_on_ticket {m n K D : ℕ} {I J : Finset (Fin m)}
    (hd : Disjoint I J) (hK : K < n) (hD : 4*n < D)
    {t : Ticket m} (ht : t ∈ tickets I J n K D) :
    ((Construction.family Flat.P (gen D I) (gen D J) n K)^2).coeff (rowKey D t.2) =
    weight I J K t := by
  classical
  rw [square_expansion I J hK hD, Polynomial.finsetSum_coeff, sum_eq_single_of_mem t ht]
  · exact Polynomial.coeff_monomial_same _ _
  · intro u hu hne
    exact Polynomial.coeff_monomial_of_ne _ (fun h => hne (ticket_injective hd hK hD hu ht h.symm))
end Autoconvolutions.Blocks
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
open scoped BigOperators
open Autoconvolutions Autoconvolutions.Blocks
namespace Autoconvolutions.Blocks
theorem _root_.solution {m n K D s : ℕ} (I J : Finset (Fin m))
    (hd : Disjoint I J) (hK : K < n) (hD : 4*n < D) (hs : s ≤ K)
    {a b : Fin m → ℕ} (ha : a ∈ goodVectors I (2*n-s)) (hb : b ∈ goodVectors J (2*n+s))
    (h : ℕ) (hh : h ≤ s) :
    ((Construction.family Flat.P (gen D I) (gen D J) n K)^2).coeff (key D a b h) =
      Estimate.height n s := by
  classical
  obtain ⟨ha₁,ha₂⟩ := goodVectors_spec ha
  obtain ⟨hb₁,hb₂⟩ := goodVectors_spec hb
  let t : Ticket m := ⟨s, ((a,b),h)⟩
  have ht : t ∈ tickets I J n K D :=
    mem_tickets.mpr ⟨by change s ≤ 2*K; omega, mem_rows.mpr ⟨ha₁,hb₁,by change h < D; omega⟩⟩
  change ((Construction.family Flat.P (gen D I) (gen D J) n K)^2).coeff (rowKey D t.2) = _
  rw [coeff_on_ticket hd hK hD ht]
  have hB : (Flat.B K s).coeff h = 1 := by
    rw [Flat.B_flat hs, Polynomial.finsetSum_coeff]
    simp [Polynomial.coeff_X_pow, hh]
  simp only [weight, t, Estimate.height, Digits.multinomial_of_distinct I a (fun i _ => ha₂ i),
    Digits.multinomial_of_distinct J b (fun i _ => hb₂ i),
    (Finset.mem_piAntidiag.mp ha₁).1, (Finset.mem_piAntidiag.mp hb₁).1, hB, mul_one]
end Autoconvolutions.Blocks
