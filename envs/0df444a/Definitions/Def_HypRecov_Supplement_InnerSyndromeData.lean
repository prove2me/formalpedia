-- Prove2me | Definitions.Def_HypRecov_Supplement_InnerSyndromeData
-- name    : HypRecov_Supplement_InnerSyndromeData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:24:08.137471+00:00
-- url     : https://prove2.me/theorems/3e50b765-9ea6-4f10-a433-23d2d70fb3f3
-- title:
--   Deterministic inner syndromes and low-degree measurements on the Boolean slice
-- statement:
--   The **inner-syndrome data** consist of a field $\mathbb F_{2^s}$, vertex labels $\gamma_v$, and the additive set label
--   $$\alpha(T)=\sum_{v\in T}\gamma_v,$$
--   together with binary encodings and uniform machines that generate labels and decode every set of size at most $r$. The required interface says that $\alpha$ is injective on all such sets, including the empty set, and that $s=O(r\log(n+1))$.
--
--   A degree-$d$ measurement on the $r$-uniform Boolean slice is the restriction of a multilinear polynomial whose monomials have size at most $d$. The module also defines the $2K$ power syndromes $S_j=\sum_e\mu_e\alpha(e)^j$ and the common exact encoder/decoder interface.
--
--   **Formalization Note** The field is Mathlib's `GaloisField 2 s`; coefficients $\mu_e$ range over the whole field, not merely $\{0,1\}$.
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Lemma A.2, p.29 (PDF p.30); Theorem A.3, pp.30-31 (PDF pp.31-32)

import Mathlib
import Definitions.Def_SpikyCVP_RunsWithin
import Definitions.Def_HypRecov_SpaceWithin
import Definitions.Def_HypRecov_encNat

set_option autoImplicit false

namespace HypRecov.Supplement

open Classical

/-- The deterministic inner-syndrome data of Lemma A.2: a characteristic-two extension field,
vertex labels, binary encodings, and a finite arithmetic description. -/
structure InnerSyndromeData (n r : ℕ) where
  s : ℕ
  label : Fin n → GaloisField 2 s
  code : GaloisField 2 s → List Bool
  code_injective : Function.Injective code
  code_length : ∀ x, (code x).length ≤ s
  description : List Bool

/-- One uniform collection of machines constructs and uses the inner-syndrome data for every
choice of `n`, `r`, and `K`. -/
structure InnerSyndromeAlgorithms where
  fieldConstructor : Turing.TM2ComputableAux Bool Bool
  labelMachine : Turing.TM2ComputableAux Bool Bool
  setDecoder : Turing.TM2ComputableAux Bool Bool
  syndromeEncoder : Turing.TM2ComputableAux Bool Bool
  syndromeDecoder : Turing.TM2ComputableAux Bool Bool

/-- The additive set label `alpha(T) = sum_{v in T} gamma_v`. -/
noncomputable def alpha {n r : ℕ} (D : InnerSyndromeData n r) (T : Finset (Fin n)) :
    GaloisField 2 D.s :=
  ∑ v ∈ T, D.label v

/-- Inputs shared by the uniform label and set-decoding machines. -/
def encInnerContext {n r : ℕ} (D : InnerSyndromeData n r) : List Bool :=
  HypRecov.encNat n ++ HypRecov.encNat r ++ HypRecov.encBits D.description

/-- The labels are injective on every set of size at most `r`, including the empty set, and the
field description, label generator and decoder have the uniform bounds of Lemma A.2. -/
def InnerSyndromeConditions {n r : ℕ} (A : InnerSyndromeAlgorithms)
    (D : InnerSyndromeData n r) (C c : ℕ) : Prop :=
  1 ≤ D.s ∧ D.s ≤ C * r * Nat.clog 2 (n + 1) ∧
  D.description.length ≤ C * D.s ∧
  Set.InjOn (alpha D) {T : Finset (Fin n) | T.card ≤ r} ∧
  SpikyCVP.RunsWithin A.fieldConstructor (HypRecov.encNat n ++ HypRecov.encNat r)
    D.description (C * (1 + n * r) ^ c) ∧
  HypRecov.SpaceWithin A.fieldConstructor (HypRecov.encNat n ++ HypRecov.encNat r)
    (C * (1 + D.s)) ∧
  (∀ v : Fin n,
    SpikyCVP.RunsWithin A.labelMachine (encInnerContext D ++ HypRecov.encNat v.val)
      (D.code (D.label v)) (C * (1 + n * r) ^ c) ∧
    HypRecov.SpaceWithin A.labelMachine (encInnerContext D ++ HypRecov.encNat v.val)
      (C * (1 + D.s + r * Nat.clog 2 (n + 1)))) ∧
  ∀ T : Finset (Fin n), T.card ≤ r →
    SpikyCVP.RunsWithin A.setDecoder (encInnerContext D ++ D.code (alpha D T)) (HypRecov.encSet T)
      (C * (1 + n * r) ^ c) ∧
    HypRecov.SpaceWithin A.setDecoder (encInnerContext D ++ D.code (alpha D T))
      (C * (1 + D.s + r * Nat.clog 2 (n + 1)))

/-- A function on the `r`-uniform Boolean slice is the restriction of a multilinear polynomial of
degree at most `d`. -/
def SliceDegreeAtMost {n : ℕ} {F : Type*} [CommSemiring F] (r d : ℕ)
    (f : {e : Finset (Fin n) // e.card = r} → F) : Prop :=
  ∃ coeff : Finset (Fin n) → F, ∀ e,
    f e = ∑ B ∈ (Finset.univ.filter (fun B : Finset (Fin n) => B.card ≤ d)),
      coeff B * if B ⊆ e.1 then 1 else 0

/-- The support of a field-valued vector on the `r`-uniform Boolean slice. -/
noncomputable def fieldSupport {n : ℕ} {F : Type*} [Zero F] (r : ℕ)
    (mu : {e : Finset (Fin n) // e.card = r} → F) :
    Finset {e : Finset (Fin n) // e.card = r} :=
  Finset.univ.filter (fun e => mu e ≠ 0)

/-- The `j`-th power syndrome `S_j = sum_e mu_e alpha(e)^j`. -/
noncomputable def powerSyndrome {n r : ℕ} (D : InnerSyndromeData n r)
    (mu : {e : Finset (Fin n) // e.card = r} → GaloisField 2 D.s) (j : ℕ) :
    GaloisField 2 D.s :=
  ∑ e, mu e * (alpha D e.1) ^ j

/-- A binary encoding of the first `2K` power syndromes. -/
noncomputable def encPowerSyndromes {n r K : ℕ} (D : InnerSyndromeData n r)
    (mu : {e : Finset (Fin n) // e.card = r} → GaloisField 2 D.s) : List Bool :=
  (List.ofFn (fun j : Fin (2 * K) => D.code (powerSyndrome D mu j.val))).flatMap HypRecov.encBits

/-- A duplicate-free encoding of the nonzero coordinates and their field coefficients. -/
noncomputable def encFieldVector {n r : ℕ} (D : InnerSyndromeData n r)
    (mu : {e : Finset (Fin n) // e.card = r} → GaloisField 2 D.s) : List Bool :=
  ((List.ofFn fun i =>
      (Fintype.equivFin {e : Finset (Fin n) // e.card = r}).symm i).filter
      (fun e => e ∈ fieldSupport r mu)).flatMap
      (fun e => true :: (HypRecov.encSet e.1 ++ HypRecov.encBits (D.code (mu e)))) ++ [false]

/-- Inputs shared by the uniform power-syndrome encoder and decoder. -/
def encPowerContext {n r : ℕ} (K : ℕ) (D : InnerSyndromeData n r) : List Bool :=
  encInnerContext D ++ HypRecov.encNat K

/-- The common deterministic decoder recovers every `K`-sparse field vector from its `2K` power
syndromes, with all measurements, description, output and workspace in the stated bit budget. -/
def PowerSyndromeGuarantee {n r K : ℕ} (A : InnerSyndromeAlgorithms)
    (D : InnerSyndromeData n r) (C c : ℕ) : Prop :=
  ∀ mu : {e : Finset (Fin n) // e.card = r} → GaloisField 2 D.s,
    (fieldSupport r mu).card ≤ K →
    SpikyCVP.RunsWithin A.syndromeEncoder (encPowerContext K D ++ encFieldVector D mu)
      (encPowerSyndromes (K := K) D mu)
      (C * (1 + n * r * K) ^ c) ∧
    HypRecov.SpaceWithin A.syndromeEncoder (encPowerContext K D ++ encFieldVector D mu)
      (C * K * r * Nat.clog 2 (n + 1)) ∧
    SpikyCVP.RunsWithin A.syndromeDecoder
      (encPowerContext K D ++ encPowerSyndromes (K := K) D mu) (encFieldVector D mu)
      (C * (1 + n * r * K) ^ c) ∧
    HypRecov.SpaceWithin A.syndromeDecoder
      (encPowerContext K D ++ encPowerSyndromes (K := K) D mu)
      (C * K * r * Nat.clog 2 (n + 1))

/-- The value of a slice measurement on a field vector. -/
noncomputable def measureVector {n r : ℕ} {F : Type*} [CommSemiring F]
    (f : {e : Finset (Fin n) // e.card = r} → F)
    (mu : {e : Finset (Fin n) // e.card = r} → F) : F :=
  ∑ e, mu e * f e

end HypRecov.Supplement


