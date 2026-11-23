-- Prove2me | solution 1 for ApproxPolySatCH.Main.aps_iff_annihilator_eval_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:38:47.062032+00:00
-- url     : https://prove2.me/submissions/befd8d15-30df-4ac2-994c-6f894e97a47d

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

open ApproxPolySatCH.Main

theorem solution {k : Type} [Field k] {n : ℕ}
    (f : Fin (n + 1) → Poly k n) (H : Poly k (n + 1))
    (hker : annihilator (extendedSystem f) =
      Ideal.span {MvPolynomial.map (algebraMap k (Constants k)) H}) :
    (APS f ↔ MvPolynomial.eval (0 : Fin (n + 1) → k) H = 0) := by
  let Hbar : Poly (Constants k) (n + 1) :=
    MvPolynomial.map (algebraMap k (Constants k)) H
  have hHmem : Hbar ∈ annihilator (extendedSystem f) := by
    rw [hker]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hHeval : MvPolynomial.eval₂ MvPolynomial.C (extendedSystem f) Hbar = 0 :=
    RingHom.mem_ker.mp hHmem
  have hF (x : Fin n → Constants k) (i : Fin (n + 1)) :
      MvPolynomial.eval₂ (algebraMap (Constants k) (Constants k)) x (extendedSystem f i) =
        MvPolynomial.eval₂ (algebraMap k (Constants k)) x (f i) := by
    rw [extendedSystem, MvPolynomial.eval₂_map]
    rfl
  have heval : MvPolynomial.eval (0 : Fin (n + 1) → Constants k) Hbar =
      algebraMap k (Constants k) (MvPolynomial.eval (0 : Fin (n + 1) → k) H) := by
    change MvPolynomial.eval (0 : Fin (n + 1) → Constants k)
      (MvPolynomial.map (algebraMap k (Constants k)) H) = _
    rw [MvPolynomial.eval_map]
    simpa using (MvPolynomial.eval₂_comp (algebraMap k (Constants k))
      (0 : Fin (n + 1) → k) H).symm
  have hzero_iff : MvPolynomial.eval (0 : Fin (n + 1) → Constants k) Hbar = 0 ↔
      MvPolynomial.eval (0 : Fin (n + 1) → k) H = 0 := by
    rw [heval]
    constructor
    · intro h
      exact (algebraMap k (Constants k)).injective (by simpa using h)
    · intro h
      rw [h, map_zero]
  rw [← hzero_iff]
  constructor
  · intro haps
    have hHvan : Hbar ∈ MvPolynomial.vanishingIdeal (Constants k)
        (Set.range (fun x : Fin n → Constants k =>
          fun i => MvPolynomial.eval₂ (algebraMap k (Constants k)) x (f i))) := by
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      rintro _ ⟨x, rfl⟩
      rw [MvPolynomial.aeval_def]
      have heq := MvPolynomial.eval₂_assoc (algebraMap (Constants k) (Constants k)) x
        (extendedSystem f) Hbar
      simpa only [hF, hHeval, MvPolynomial.eval₂_zero] using heq
    exact MvPolynomial.mem_zeroLocus_iff.mp haps Hbar hHvan
  · intro hzero
    change (0 : Fin (n + 1) → Constants k) ∈ MvPolynomial.zeroLocus (Constants k)
      (MvPolynomial.vanishingIdeal (Constants k)
        (Set.range (fun x : Fin n → Constants k =>
          fun i => MvPolynomial.eval₂ (algebraMap k (Constants k)) x (f i))))
    rw [MvPolynomial.mem_zeroLocus_iff]
    intro P hP
    have hPker : P ∈ annihilator (extendedSystem f) := by
      change P ∈ RingHom.ker (MvPolynomial.eval₂Hom MvPolynomial.C (extendedSystem f))
      rw [RingHom.mem_ker]
      apply MvPolynomial.funext
      intro x
      have hv := MvPolynomial.mem_vanishingIdeal_iff.mp hP
        (fun i => MvPolynomial.eval₂ (algebraMap k (Constants k)) x (f i)) ⟨x, rfl⟩
      rw [MvPolynomial.aeval_def] at hv
      have heq := MvPolynomial.eval₂_assoc (algebraMap (Constants k) (Constants k)) x
        (extendedSystem f) P
      have heq' : MvPolynomial.eval₂ (algebraMap (Constants k) (Constants k))
          (fun i => MvPolynomial.eval₂ (algebraMap k (Constants k)) x (f i)) P =
          MvPolynomial.eval₂ (algebraMap (Constants k) (Constants k)) x
            (MvPolynomial.eval₂ MvPolynomial.C (extendedSystem f) P) := by
        simpa only [hF] using heq
      exact heq'.symm.trans hv
    rw [hker, Ideal.mem_span_singleton] at hPker
    obtain ⟨Q, hPQ⟩ := hPker
    change MvPolynomial.eval (0 : Fin (n + 1) → Constants k) P = 0
    rw [hPQ]
    change MvPolynomial.eval (0 : Fin (n + 1) → Constants k) (Hbar * Q) = 0
    rw [MvPolynomial.eval_mul, hzero, zero_mul]
