-- Prove2me | Definitions.Def_BCFGJPSSV26_Combine_PolyTime
-- name    : BCFGJPSSV26_Combine_PolyTime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:13:17.779246+00:00
-- url     : https://prove2.me/theorems/ee46be41-bf08-466e-8cf6-e6e77048b89d
-- title:
--   BCFGJPSSV26.Combine.PolyTime — The algorithm of Theorem 1.1 runs in polynomial time
-- statement:
--   This is module `BCFGJPSSV26.Combine.PolyTime` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   Certificates (`Turing.MultiTapeTM.ComputableInPolyTime`) for the algorithm on its coins,
--   `BCFGJPSSV26.Combine.Prm.alg'` (`BCFGJPSSV26.Combine.Prm.alg'_polytime`), from the certificates of
--   `A₂` (polynomial time) and `A₃` (time `O(2^(e L) (N + 2)^e + |(x, r)|)`). The algorithm of
--   Theorem 1.3 reads its accuracy `ε` as an input; given a fixed `ε`, it is such an `A₃`, with
--   `e = a (⌈1/ε⌉ + 1)^b`, since the encoding of `ε` has a fixed length
--   (`BCFGJPSSV26.Combine.runsInTime_fix`).
--
--   A run of `A₃` is polynomial-time on the inputs the algorithm gives it
--   (`BCFGJPSSV26.Combine.Prm.run₃_polytime`, by
--   `Turing.MultiTapeTM.ComputableInO.computableInPolyTime_comp`): there
--   `L = M (K ⌈log₂(n + 1)⌉ + 1)`, so that `2^(e L) ≤ 2^(e M (K + 1)) (N + 1)^(e M K)` on an instance
--   of encoded length `N` (`BCFGJPSSV26.Combine.Prm.two_pow_Lp_le`). The algorithm maps it over the
--   runs (`Turing.MultiTapeTM.ComputableInPolyTime.mapWithInput`) like any polynomial-time function.
--   The number of coins it reads is polynomial too (`BCFGJPSSV26.Combine.Prm.coinLen_le`).
--
--   Encodings: the instance and the outputs as in `BCFGJPSSV26/Model.lean`, numbers of centers in
--   binary, numbers of runs and of coins in unary.
--
--   **Contents.** The module is published as a whole: 35 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Combine_PolyTime`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Combine/PolyTime.lean

module

public import Definitions.Def_BCFGJPSSV26_Combine_Algorithm
public import Definitions.Def_BuhaiPapers_Background_BlackBox
public import Definitions.Def_BuhaiPapers_Background_PolyTime_Rat
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_EraseDupsBy
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Binary

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Combine.PolyTime` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The algorithm of Theorem 1.1 runs in polynomial time

Certificates (`Turing.MultiTapeTM.ComputableInPolyTime`) for the algorithm on its coins,
`BCFGJPSSV26.Combine.Prm.alg'` (`BCFGJPSSV26.Combine.Prm.alg'_polytime`), from the certificates of
`A₂` (polynomial time) and `A₃` (time `O(2^(e L) (N + 2)^e + |(x, r)|)`). The algorithm of
Theorem 1.3 reads its accuracy `ε` as an input; given a fixed `ε`, it is such an `A₃`, with
`e = a (⌈1/ε⌉ + 1)^b`, since the encoding of `ε` has a fixed length
(`BCFGJPSSV26.Combine.runsInTime_fix`).

A run of `A₃` is polynomial-time on the inputs the algorithm gives it
(`BCFGJPSSV26.Combine.Prm.run₃_polytime`, by
`Turing.MultiTapeTM.ComputableInO.computableInPolyTime_comp`): there
`L = M (K ⌈log₂(n + 1)⌉ + 1)`, so that `2^(e L) ≤ 2^(e M (K + 1)) (N + 1)^(e M K)` on an instance
of encoded length `N` (`BCFGJPSSV26.Combine.Prm.two_pow_Lp_le`). The algorithm maps it over the
runs (`Turing.MultiTapeTM.ComputableInPolyTime.mapWithInput`) like any polynomial-time function.
The number of coins it reads is polynomial too (`BCFGJPSSV26.Combine.Prm.coinLen_le`).

Encodings: the instance and the outputs as in `BCFGJPSSV26/Model.lean`, numbers of centers in
binary, numbers of runs and of coins in unary.
-/

@[expose] public section

namespace BCFGJPSSV26.Combine

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

variable {α : Type} {input : α ↪ List Bool}

/-! ### Bounds -/

theorem two_pow_size_le (n : ℕ) : 2 ^ n.size ≤ 2 * n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hs : 0 < n.size := Nat.size_pos.2 hn
    have h : 2 ^ (n.size - 1) ≤ n := Nat.lt_size.1 (by omega)
    have : 2 ^ n.size = 2 * 2 ^ (n.size - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega

namespace Prm

variable (P : Prm)

/-- **`2^(e L)` is polynomial in the instance.** -/
theorem two_pow_Lp_le (I : Instance) :
    2 ^ (P.e * P.Lp I) ≤
      2 ^ (P.e * P.M * (P.K + 1)) * ((encInstance I).length + 1) ^ (P.e * P.M * P.K) := by
  have hn := n_le_length I
  have h2 : 2 ^ I.n.size ≤ 2 * ((encInstance I).length + 1) :=
    (two_pow_size_le _).trans (by omega)
  have he : P.e * P.Lp I = I.n.size * (P.e * P.M * P.K) + P.e * P.M := by
    unfold Lp cnt
    ring
  calc 2 ^ (P.e * P.Lp I) = (2 ^ I.n.size) ^ (P.e * P.M * P.K) * 2 ^ (P.e * P.M) := by
        rw [he, pow_add, pow_mul]
    _ ≤ (2 * ((encInstance I).length + 1)) ^ (P.e * P.M * P.K) * 2 ^ (P.e * P.M) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h2 _)
    _ = 2 ^ (P.e * P.M * (P.K + 1)) * ((encInstance I).length + 1) ^ (P.e * P.M * P.K) := by
        rw [mul_pow, mul_add, pow_add]
        ring

/-- The coins of a run, at most. -/
theorem blockLen_le (I : Instance) :
    P.blockLen I ≤ 2 ^ (P.e * P.M * (P.K + 1)) * 2 ^ P.e *
      ((encInstance I).length + 1) ^ (P.e * P.M * P.K + P.e) := by
  unfold blockLen
  have h2 : ((encInstance I).length + 2) ^ P.e ≤ 2 ^ P.e * ((encInstance I).length + 1) ^ P.e := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by omega) _
  calc 2 ^ (P.e * P.Lp I) * ((encInstance I).length + 2) ^ P.e
      ≤ (2 ^ (P.e * P.M * (P.K + 1)) * ((encInstance I).length + 1) ^ (P.e * P.M * P.K)) *
          (2 ^ P.e * ((encInstance I).length + 1) ^ P.e) := Nat.mul_le_mul (P.two_pow_Lp_le I) h2
    _ = _ := by rw [pow_add]; ring

/-- Each run of `A₃` reads at most a block of coins. -/
theorem stableTime_le_blockLen (I : Instance) (j : ℕ) :
    stableTime P.e (atK I j, P.Lp I) ≤ P.blockLen I := by
  unfold stableTime blockLen
  refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
  have := length_encInstance_setK_le (I := I) (k := k₀ I - j) (by unfold k₀; omega)
  exact Nat.add_le_add_right this 2

/-- **The number of coins is polynomial.** -/
theorem coinLen_le (I : Instance) :
    P.coinLen I ≤ (P.K + 1) * (2 ^ (P.e * P.M * (P.K + 1)) * 2 ^ P.e) *
      ((encInstance I).length + 2) ^ (P.e * P.M * P.K + P.e + 1) := by
  have hn := n_le_length I
  have hs : I.n.size ≤ I.n := (Nat.size_le.2 Nat.lt_two_pow_self)
  have hc : P.cnt I ≤ (P.K + 1) * ((encInstance I).length + 2) := by
    unfold cnt
    have := Nat.mul_le_mul_left P.K (hs.trans hn)
    nlinarith
  have hb := P.blockLen_le I
  have hb' : P.blockLen I ≤ 2 ^ (P.e * P.M * (P.K + 1)) * 2 ^ P.e *
      ((encInstance I).length + 2) ^ (P.e * P.M * P.K + P.e) :=
    hb.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  unfold coinLen
  calc P.cnt I * P.blockLen I ≤ ((P.K + 1) * ((encInstance I).length + 2)) *
        (2 ^ (P.e * P.M * (P.K + 1)) * 2 ^ P.e *
          ((encInstance I).length + 2) ^ (P.e * P.M * P.K + P.e)) := Nat.mul_le_mul hc hb'
    _ = _ := by rw [pow_succ]; ring

end Prm

/-! ### Instances -/

/-- The number of clients. -/
theorem n_polytime : ComputableInPolyTime (fun I : Instance ↦ I.n) encInstance encNat :=
  (fst _ _).comp (of_eq (encOut := encPair encNat (encPair encNat (encPair encNat
    (encList (encList encRat))))) (f := fun I : Instance ↦ (I.n, I.m, I.k, distTable I))
    fun _ ↦ rfl)

/-- The number of facilities. -/
theorem m_polytime : ComputableInPolyTime (fun I : Instance ↦ I.m) encInstance encNat :=
  ((fst _ _).comp (snd _ _)).comp (of_eq (encOut := encPair encNat (encPair encNat
    (encPair encNat (encList (encList encRat))))) (f := fun I : Instance ↦
      (I.n, I.m, I.k, distTable I)) fun _ ↦ rfl)

/-- The number of centers. -/
theorem k_polytime : ComputableInPolyTime (fun I : Instance ↦ I.k) encInstance encNat :=
  (((fst _ _).comp (snd _ _)).comp (snd _ _)).comp (of_eq (encOut := encPair encNat
    (encPair encNat (encPair encNat (encList (encList encRat))))) (f := fun I : Instance ↦
      (I.n, I.m, I.k, distTable I)) fun _ ↦ rfl)

/-- The table of distances. -/
theorem table_polytime :
    ComputableInPolyTime (fun I : Instance ↦ distTable I) encInstance (encList (encList encRat)) :=
  (((snd _ _).comp (snd _ _)).comp (snd _ _)).comp (of_eq (encOut := encPair encNat
    (encPair encNat (encPair encNat (encList (encList encRat))))) (f := fun I : Instance ↦
      (I.n, I.m, I.k, distTable I)) fun _ ↦ rfl)

/-- Another number of centers. -/
theorem setK_polytime {f : α → Instance} {g : α → ℕ}
    (hf : ComputableInPolyTime f input encInstance) (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ setK (f a) (g a)) input encInstance :=
  ((n_polytime.comp hf).prod ((m_polytime.comp hf).prod
    (hg.prod (table_polytime.comp hf)))).of_enc_eq fun _ ↦ encInstance_setK _ _

theorem k₀_polytime : ComputableInPolyTime k₀ encInstance encNat := by
  have h := ite_decide (condition := fun I : Instance ↦ I.k ≤ I.m)
    (binary_le' k_polytime m_polytime) k_polytime m_polytime
  refine h.of_enc_eq fun I ↦ ?_
  unfold k₀
  rw [min_def]

/-! ### Exact costs and the choice of the output -/

theorem minQ_polytime {l : α → List ℚ} (hl : ComputableInPolyTime l input (encList encRat)) :
    ComputableInPolyTime (fun a ↦ minQ (l a)) input encRat := by
  unfold minQ
  have htest : ComputableInPolyTime (fun p : α × ℚ ↦ (l p.1).all fun q' ↦ decide (p.2 ≤ q'))
      (encPair input encRat) encBool :=
    allWithInput (test := fun (p : α × ℚ) (q' : ℚ) ↦ decide (p.2 ≤ q')) (hl.comp (fst _ _))
      (rat_le' ((snd _ _).comp (fst _ _)) (snd _ _))
  have h := (optionGetD encRat).comp ((findWithInput
    (test := fun a q ↦ (l a).all fun q' ↦ decide (q ≤ q')) hl htest).prod
      (const (encIn := input) (0 : ℚ)))
  exact h

theorem costQ_polytime {n : α → ℕ} {T : α → List (List ℚ)} {S : α → List ℕ}
    (hn : ComputableInPolyTime n input encNat)
    (hT : ComputableInPolyTime T input (encList (encList encRat)))
    (hS : ComputableInPolyTime S input (encList encNat)) :
    ComputableInPolyTime (fun a ↦ costQ (n a) (T a) (S a)) input encRat := by
  unfold costQ
  have hrange : ComputableInPolyTime (fun a ↦ List.range (min (T a).length (n a))) input
      (encList encUnary) :=
    unary_range' (binary_min_unary' ((length_list _).comp hT) hn)
  have hrow : ComputableInPolyTime (fun p : (α × ℕ) × ℕ ↦ (T p.1.1).getD p.1.2 [])
      (encPair (encPair input encUnary) encNat) (encList encRat) :=
    listGetDWithInput (hT.comp ((fst _ _).comp (fst _ _))) ((snd _ _).comp (fst _ _)) []
  have hidx : ComputableInPolyTime (fun p : (α × ℕ) × ℕ ↦ n p.1.1 + p.2)
      (encPair (encPair input encUnary) encNat) encNat :=
    .of_tidy (ComputableTidilyInPolyTime.binary_add'
      (hn.comp ((fst _ _).comp (fst _ _))).tidy (snd _ _).tidy)
  have hentry := listGetD_binary (encA := encRat) (0 : ℚ) hrow hidx
  have hlist : ComputableInPolyTime
      (fun p : α × ℕ ↦ (S p.1).map fun i ↦ (T p.1).getD p.2 [] |>.getD (n p.1 + i) 0)
      (encPair input encUnary) (encList encRat) :=
    mapWithInput (f := fun (p : α × ℕ) (i : ℕ) ↦ (T p.1).getD p.2 [] |>.getD (n p.1 + i) 0)
      (hS.comp (fst _ _)) hentry
  exact rat_sum' (mapWithInput (f := fun a j ↦ minQ ((S a).map fun i ↦
    (T a).getD j [] |>.getD (n a + i) 0)) hrange (minQ_polytime hlist))

theorem valid_polytime {m k : α → ℕ} {S : α → List ℕ}
    (hm : ComputableInPolyTime m input encNat) (hk : ComputableInPolyTime k input encNat)
    (hS : ComputableInPolyTime S input (encList encNat)) :
    ComputableInPolyTime (fun a ↦ valid (m a) (k a) (S a)) input encBool := by
  unfold valid
  have h1 : ComputableInPolyTime (fun a ↦ !(S a).isEmpty) input encBool :=
    bool_not.comp ((listIsEmpty (encA := encNat)).comp hS)
  have h2 : ComputableInPolyTime (fun a ↦ decide (S a).Nodup) input encBool := decide_nodup hS
  have h3 : ComputableInPolyTime (fun a ↦ (S a).all fun i ↦ decide (i < m a)) input encBool :=
    allWithInput (test := fun a i ↦ decide (i < m a)) hS (binary_lt' (snd _ _) (hm.comp (fst _ _)))
  have h4 : ComputableInPolyTime (fun a ↦ decide ((S a).length ≤ k a)) input encBool :=
    binary_le' (unary_to_binary.comp ((length_list _).comp hS)) hk
  exact bool_and' (bool_and' (bool_and' h1 h2) h3) h4

theorem best_polytime {n m k : α → ℕ} {T : α → List (List ℚ)} {cs : α → List (List ℕ)}
    (hn : ComputableInPolyTime n input encNat) (hm : ComputableInPolyTime m input encNat)
    (hk : ComputableInPolyTime k input encNat)
    (hT : ComputableInPolyTime T input (encList (encList encRat)))
    (hcs : ComputableInPolyTime cs input (encList (encList encNat))) :
    ComputableInPolyTime (fun a ↦ best (n a) (m a) (k a) (T a) (cs a)) input (encList encNat) := by
  unfold best bestOf
  have hvs : ComputableInPolyTime (fun a ↦ (cs a).filter (valid (m a) (k a))) input
      (encList (encList encNat)) :=
    filterWithInput (test := fun a ↦ valid (m a) (k a)) hcs
      (valid_polytime (hm.comp (fst _ _)) (hk.comp (fst _ _)) (snd _ _))
  have hc₁ : ComputableInPolyTime
      (fun q : (α × List ℕ) × List ℕ ↦ costQ (n q.1.1) (T q.1.1) q.1.2)
      (encPair (encPair input (encList encNat)) (encList encNat)) encRat :=
    costQ_polytime (hn.comp ((fst _ _).comp (fst _ _))) (hT.comp ((fst _ _).comp (fst _ _)))
      ((snd _ _).comp (fst _ _))
  have hc₂ : ComputableInPolyTime
      (fun q : (α × List ℕ) × List ℕ ↦ costQ (n q.1.1) (T q.1.1) q.2)
      (encPair (encPair input (encList encNat)) (encList encNat)) encRat :=
    costQ_polytime (hn.comp ((fst _ _).comp (fst _ _))) (hT.comp ((fst _ _).comp (fst _ _)))
      (snd _ _)
  have htest : ComputableInPolyTime (fun p : α × List ℕ ↦ ((cs p.1).filter (valid (m p.1)
      (k p.1))).all fun S' ↦ decide (costQ (n p.1) (T p.1) p.2 ≤ costQ (n p.1) (T p.1) S'))
      (encPair input (encList encNat)) encBool :=
    allWithInput (test := fun (p : α × List ℕ) S' ↦
      decide (costQ (n p.1) (T p.1) p.2 ≤ costQ (n p.1) (T p.1) S')) (hvs.comp (fst _ _))
      (rat_le' hc₁ hc₂)
  have h := (optionGetD (encList encNat)).comp ((findWithInput (test := fun a S ↦
    ((cs a).filter (valid (m a) (k a))).all fun S' ↦
      decide (costQ (n a) (T a) S ≤ costQ (n a) (T a) S')) hvs htest).prod
        (const (encIn := input) [0]))
  exact h

/-! ### The algorithm of Theorem 1.3 for a fixed accuracy -/

/-- **The algorithm of Theorem 1.3 for a fixed `ε`**, on inputs `((I, L), r)`: it runs within
`O(stableTime e (I, L) + |((I, L), r)|)` with `e = a (⌈1/ε⌉ + 1)^b`, since the encoding of `ε` has
a fixed length. -/
theorem runsInTime_fix {A : ((Instance × ℕ) × ℚ) × List Bool → List ℕ} {a b : ℕ}
    (hA : RunsInTime (encPair (encPair encInstance encUnary) encRat) encCenters A
      (stableTimeOf a b)) (ε : ℚ) :
    ∃ c, ComputableInTimeAndSpace (fun y : (Instance × ℕ) × List Bool ↦ A ((y.1, ε), y.2))
      (encPair (encPair encInstance encUnary) encBits) (encList encNat)
      (fun y ↦ c * (stableTime (a * (⌈1 / ε⌉₊ + 1) ^ b) y.1 +
        (encPair (encPair encInstance encUnary) encBits y).length + 1))
      (fun y ↦ c * (stableTime (a * (⌈1 / ε⌉₊ + 1) ^ b) y.1 +
        (encPair (encPair encInstance encUnary) encBits y).length + 1)) := by
  obtain ⟨c, hc⟩ := hA
  have hg := ((ComputableInO.fst (encPair encInstance encUnary) encBits).prod
    (ComputableInO.const (encMid := encRat) ε)).prod (ComputableInO.snd _ encBits)
  have h := hc.computableInO.comp' hg
  set K := 3 + 3 * c * ((encRat ε).length + 3)
  have hb : ∀ y : (Instance × ℕ) × List Bool,
      (encPair (encPair encInstance encUnary) encBits y).length +
        (encPair (encPair encInstance encUnary) encBits y).length +
        (encPair (encPair encInstance encUnary) encBits y).length +
        c * (stableTimeOf a b (y.1, ε) + (encPair (encPair (encPair encInstance encUnary) encRat)
          encBits ((y.1, ε), y.2)).length + 1) ≤
      K * (stableTime (a * (⌈1 / ε⌉₊ + 1) ^ b) y.1 +
        (encPair (encPair encInstance encUnary) encBits y).length + 1) := by
    intro y
    have hst : stableTimeOf a b (y.1, ε) = stableTime (a * (⌈1 / ε⌉₊ + 1) ^ b) y.1 := rfl
    have h1 : (encPair (encPair encInstance encUnary) encBits y).length =
        2 * (encPair encInstance encUnary y.1).length + 1 + (encBits y.2).length :=
      length_encPair _
    have h2 : (encPair (encPair (encPair encInstance encUnary) encRat) encBits
        ((y.1, ε), y.2)).length = 2 * (2 * (encPair encInstance encUnary y.1).length + 1 +
          (encRat ε).length) + 1 + (encBits y.2).length := by
      rw [length_encPair, length_encPair]
    rw [hst, h1, h2]
    generalize stableTime (a * (⌈1 / ε⌉₊ + 1) ^ b) y.1 = S
    generalize (encPair encInstance encUnary y.1).length = X
    generalize (encBits y.2).length = R
    simp only [K]
    generalize (encRat ε).length = Q
    have h3 : S + (2 * (2 * X + 1 + Q) + 1 + R) + 1 ≤ 3 * (Q + 3) * (S + (2 * X + 1 + R) + 1) := by
      nlinarith
    have h4 : c * (S + (2 * (2 * X + 1 + Q) + 1 + R) + 1) ≤
        3 * c * (Q + 3) * (S + (2 * X + 1 + R) + 1) :=
      calc c * (S + (2 * (2 * X + 1 + Q) + 1 + R) + 1)
          ≤ c * (3 * (Q + 3) * (S + (2 * X + 1 + R) + 1)) := Nat.mul_le_mul_left _ h3
        _ = 3 * c * (Q + 3) * (S + (2 * X + 1 + R) + 1) := by ring
    have e : (3 + 3 * c * (Q + 3)) * (S + (2 * X + 1 + R) + 1) = 3 * (S + (2 * X + 1 + R) + 1) +
        3 * c * (Q + 3) * (S + (2 * X + 1 + R) + 1) := by ring
    rw [e]
    omega
  obtain ⟨c', hc', -⟩ := h.mono (T' := fun y ↦ stableTime (a * (⌈1 / ε⌉₊ + 1) ^ b) y.1 +
      (encPair (encPair encInstance encUnary) encBits y).length)
    (S' := fun y ↦ stableTime (a * (⌈1 / ε⌉₊ + 1) ^ b) y.1 +
      (encPair (encPair encInstance encUnary) encBits y).length) K hb hb
  exact ⟨c', hc'⟩

/-! ### The algorithm -/

namespace Prm

variable (P : Prm)

/-- An instance with coins. -/
abbrev encX : Instance × List Bool ↪ List Bool := encPair encInstance encBits

/-- An instance with coins and the number of a run. -/
abbrev encXJ : (Instance × List Bool) × ℕ ↪ List Bool := encPair encX encUnary

/-- The input of `A₃`. -/
abbrev enc₃ : (Instance × ℕ) × List Bool ↪ List Bool :=
  encPair (encPair encInstance encUnary) encBits

theorem cnt_polytime : ComputableInPolyTime P.cnt encInstance encUnary := by
  have h := unary_add' (unary_mul' (const (encIn := encInstance) P.K)
    (binary_size.comp n_polytime)) (const (encIn := encInstance) 1)
  exact h

theorem Lp_polytime : ComputableInPolyTime P.Lp encInstance encUnary := by
  have h := unary_mul' (const (encIn := encInstance) P.M) P.cnt_polytime
  exact h

theorem runs_polytime : ComputableInPolyTime P.runs encInstance encUnary := by
  have h := binary_min_unary' P.cnt_polytime k₀_polytime
  exact h

theorem twoPow_polytime :
    ComputableInPolyTime (fun I ↦ 2 ^ (P.e * P.Lp I)) encInstance encUnary := by
  have hL := unary_mul' (const (encIn := encInstance) P.e) P.Lp_polytime
  exact unary_two_pow hL (PolyBounded.of_forall_le _ _ P.two_pow_Lp_le)

theorem blockLen_polytime : ComputableInPolyTime P.blockLen encInstance encUnary := by
  have h := unary_mul' P.twoPow_polytime ((unary_pow P.e).comp
    (unary_add' (encoding_length encInstance) (const (encIn := encInstance) 2)))
  exact h

theorem coinLen_polytime : ComputableInPolyTime P.coinLen encInstance encUnary := by
  have h := unary_mul' P.cnt_polytime P.blockLen_polytime
  exact h

theorem atK_polytime {f : α → Instance} {j : α → ℕ}
    (hf : ComputableInPolyTime f input encInstance) (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime (fun a ↦ atK (f a) (j a)) input encInstance := by
  have h := setK_polytime hf (binary_sub' (k₀_polytime.comp hf) (unary_to_binary.comp hj))
  exact h

theorem stableTime_polytime {f : α → Instance} {j : α → ℕ}
    (hf : ComputableInPolyTime f input encInstance) (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime (fun a ↦ stableTime P.e (atK (f a) (j a), P.Lp (f a))) input
      encUnary := by
  have h := unary_mul' (P.twoPow_polytime.comp hf) ((unary_pow P.e).comp
    (unary_add' ((encoding_length encInstance).comp (atK_polytime hf hj))
      (const (encIn := input) 2)))
  exact h

theorem coins_polytime :
    ComputableInPolyTime (fun p : (Instance × List Bool) × ℕ ↦ P.coins p.1.1 p.1.2 p.2) encXJ
      encBits := by
  have hI : ComputableInPolyTime (fun p : (Instance × List Bool) × ℕ ↦ p.1.1) encXJ
      encInstance := (fst _ _).comp (fst _ _)
  have hr : ComputableInPolyTime (fun p : (Instance × List Bool) × ℕ ↦ p.1.2) encXJ encBits :=
    (snd _ _).comp (fst _ _)
  have hj : ComputableInPolyTime (fun p : (Instance × List Bool) × ℕ ↦ p.2) encXJ encUnary :=
    snd _ _
  have h := bitsTakeWithInput (bitsDropWithInput hr (unary_mul' hj (P.blockLen_polytime.comp hI)))
    (P.stableTime_polytime hI hj)
  exact h

/-- The input of run `j` of `A₃`. -/
def pre₃ (p : (Instance × List Bool) × ℕ) : (Instance × ℕ) × List Bool :=
  ((atK p.1.1 p.2, P.Lp p.1.1), P.coins p.1.1 p.1.2 p.2)

theorem pre₃_polytime : ComputableInPolyTime P.pre₃ encXJ enc₃ := by
  have hI : ComputableInPolyTime (fun p : (Instance × List Bool) × ℕ ↦ p.1.1) encXJ
      encInstance := (fst _ _).comp (fst _ _)
  have hj : ComputableInPolyTime (fun p : (Instance × List Bool) × ℕ ↦ p.2) encXJ encUnary :=
    snd _ _
  have h := ((atK_polytime hI hj).prod (P.Lp_polytime.comp hI)).prod P.coins_polytime
  exact h

theorem length_encInstance_le (p : (Instance × List Bool) × ℕ) :
    (encInstance p.1.1).length ≤ (encXJ p).length := by
  simp only [encXJ, encX, length_encPair]
  omega

/-- **A run of `A₃` is polynomial-time**, on the inputs the algorithm gives it. -/
theorem run₃_polytime {c : ℕ} (hA₃ : ComputableInTimeAndSpace P.A₃ enc₃ (encList encNat)
      (fun y ↦ c * (stableTime P.e y.1 + (enc₃ y).length + 1))
      (fun y ↦ c * (stableTime P.e y.1 + (enc₃ y).length + 1))) :
    ComputableInPolyTime (fun p : (Instance × List Bool) × ℕ ↦ P.run₃ p.1 p.2) encXJ
      (encList encNat) := by
  have hst : PolyBounded (fun p ↦ (encXJ p).length)
      (fun p : (Instance × List Bool) × ℕ ↦ stableTime P.e (atK p.1.1 p.2, P.Lp p.1.1)) :=
    PolyBounded.of_forall_le _ _ fun p ↦ (P.stableTime_le_blockLen p.1.1 p.2).trans
      ((P.blockLen_le p.1.1).trans (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (by have := length_encInstance_le p; omega) _)))
  have hb : PolyBounded (fun p ↦ (encXJ p).length) fun p ↦
      c * (stableTime P.e (P.pre₃ p).1 + (enc₃ (P.pre₃ p)).length + 1) :=
    (PolyBounded.const c).mul ((hst.add P.pre₃_polytime.polyBounded_length).add (.const 1))
  exact hA₃.computableInO.computableInPolyTime_comp P.pre₃_polytime hb hb

theorem run₂_polytime (hA₂ : ComputableInPolyTime P.A₂ encInstance (encList encNat)) :
    ComputableInPolyTime P.run₂ encInstance (encList (encList encNat)) := by
  have hc := unary_to_binary.comp P.cnt_polytime
  have hlt := binary_lt' hc k₀_polytime
  have hs := hA₂.comp (setK_polytime id' (binary_sub' k₀_polytime hc))
  have h := ite_decide (condition := fun I ↦ P.cnt I < k₀ I) hlt
    (cons' hs (const (encIn := encInstance) [])) (const (encIn := encInstance) [])
  exact h

theorem cands_polytime (hA₂ : ComputableInPolyTime P.A₂ encInstance (encList encNat))
    {c : ℕ} (hA₃ : ComputableInTimeAndSpace P.A₃ enc₃ (encList encNat)
      (fun y ↦ c * (stableTime P.e y.1 + (enc₃ y).length + 1))
      (fun y ↦ c * (stableTime P.e y.1 + (enc₃ y).length + 1))) :
    ComputableInPolyTime P.cands encX (encList (encList encNat)) := by
  have hI : ComputableInPolyTime (fun x : Instance × List Bool ↦ x.1) encX encInstance :=
    fst _ _
  have hmap := mapWithInput (f := P.run₃) (unary_range' (P.runs_polytime.comp hI))
    (P.run₃_polytime hA₃)
  have h := listAppend' ((P.run₂_polytime hA₂).comp hI) hmap
  exact h

/-- **The algorithm on its coins runs in polynomial time.** -/
theorem alg'_polytime (hA₂ : ComputableInPolyTime P.A₂ encInstance (encList encNat))
    {c : ℕ} (hA₃ : ComputableInTimeAndSpace P.A₃ enc₃ (encList encNat)
      (fun y ↦ c * (stableTime P.e y.1 + (enc₃ y).length + 1))
      (fun y ↦ c * (stableTime P.e y.1 + (enc₃ y).length + 1))) :
    ComputableInPolyTime P.alg' encX (encList encNat) := by
  have hI : ComputableInPolyTime (fun x : Instance × List Bool ↦ x.1) encX encInstance :=
    fst _ _
  have h := best_polytime (n_polytime.comp hI) (m_polytime.comp hI) (k_polytime.comp hI)
    (table_polytime.comp hI) (P.cands_polytime hA₂ hA₃)
  exact h

end Prm

end BCFGJPSSV26.Combine


