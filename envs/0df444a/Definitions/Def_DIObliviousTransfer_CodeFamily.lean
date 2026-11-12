-- Prove2me | Definitions.Def_DIObliviousTransfer_CodeFamily
-- name    : DIObliviousTransfer_CodeFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T09:03:05.789845+00:00
-- url     : https://prove2.me/theorems/ac460f56-231b-43af-be61-0831e6a998c9
-- title:
--   The code interface over $\mathbb F_{64}$ (Lemmas 5–6) and admissible lengths
-- statement:
--   The field is $\mathbb F_{64}$ with a fixed $\mathbb F_2$-basis $e_1,\dots,e_6$. The admissible code lengths are $m_j=\lfloor100N_j/101\rfloor$ with $N_j=56\cdot8^j$ for $j\ge1$, and $\mathrm{Next}(a)$ is the first admissible length at least $\max\{443,a\}$.
--
--   A **code family** gives, for each length $m$ and secret capacity $q$:
--   1. codes $B=D$ and $A$ in $\mathbb F_{64}^m$ with linear secret maps onto $\mathbb F_{64}^q$;
--   2. affine parametrizations of the secret fibers;
--   3. a decoder for the twisted code $A^\sigma=\sigma*A$ with erasures and an error budget;
--   4. erasure extension into $D$ and $A^\sigma$.
--
--   **CodeFamily.Spec** requires, for admissible $m$ and $1\le q\le\lfloor m/100\rfloor$, exactly the conclusions of Lemmas 5 and 6:
--   - $B*D\subseteq A$ and $\mathrm{sec}(b*d)=\mathrm{sec}(b)*\mathrm{sec}(d)$;
--   - the secret maps are onto;
--   - $d(B_0^\perp)\ge0.048m+1$, $d(D)\ge0.65m$ and $d(A)\ge0.30m$;
--   - the fiber parametrizations are bijective;
--   - the decoder succeeds whenever $2T+|E|\le0.15m$ and never returns a word outside its budget;
--   - the extensions are correct;
--   - all of these operations run in polynomial time.
--
--   **Formalization Note** This is decision D15. Mathlib has no Riemann–Roch spaces, so the protocols are stated for every family meeting this interface. The paper's algebraic-geometry family on the Garcia–Stichtenoth tower is one such family.
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), §3.2, pp.24–26, Lemmas 5–6; Fact 5, p.16

import Mathlib
import Definitions.Def_DIObliviousTransfer_Negligible

namespace DIObliviousTransfer

/-!
Batra, Chen, Jain, Zhang, arXiv:2610.01421 (held version, sha256 8334c039…), §3.2, pp.24–26:
the field `F₆₄`, the admissible code lengths, and the code interface (Lemmas 5 and 6).

"For the tower in Fact 5, use the admissible lengths `m_j = ⌊100N_j/101⌋`, `j ≥ 1`. … Let
`Next(a)` be the first admissible length at least `max{443, a}`." (p.25), with `N_j = 56 · 8^j`
(Fact 5, p.16).

**Formalization Note** (decision D15, a generalization). The paper's codes are algebraic-geometry
codes `B = D = ev_P L(G)`, `A = ev_P L(2G)` on the Garcia–Stichtenoth tower; Mathlib has no
Riemann–Roch spaces. The protocols are therefore parametrized by a `CodeFamily` carrying, for each
admissible `m` and `1 ≤ q ≤ ⌊m/100⌋`, exactly the conclusions of Lemma 5 (multiplication
compatibility, surjective secret maps, the distances `d(B₀^⊥) ≥ 0.048m + 1` (from its proof),
`d(D) ≥ 0.65m`, `d(A) ≥ 0.30m`, polynomial-time operations) and of Lemma 6 (a decoder for `A^σ`
correct whenever `2T + |E| ≤ 0.15m`, which the AG family meets since `m − 2deg G − g > 0.15m`).
The secret maps are linear maps on all of `F₆₄^m`; only their values on the codes are used.
Uniform sampling in a secret fiber is an affine parametrization by free coefficients ("A nonempty
fiber is an affine space, so independent uniform field coefficients sample it uniformly", p.25).
Twists are `C^σ = σ ∗ C` and `sec_σ(v) = sec(σ^{-1} ∗ v)` (p.25). `F₆₄` is `GaloisField 2 6`
with the fixed `F₂`-basis `basisE`; a field element is encoded by its six basis coordinates.
-/

/-- The field `F₆₄`. -/
abbrev F64 := GaloisField 2 6

noncomputable instance : Fintype F64 := Fintype.ofFinite F64
noncomputable instance : DecidableEq F64 := Classical.decEq F64

/-- The fixed `F₂`-basis `e₁, …, e₆` of `F₆₄` (p.28, "a fixed F₂-basis"). -/
noncomputable def basisE : Module.Basis (Fin 6) (ZMod 2) F64 :=
  Module.finBasisOfFinrankEq (ZMod 2) F64 (GaloisField.finrank 2 (by norm_num))

/-- Six bits as a field element `Σ_j b_j e_j`. -/
noncomputable def f64OfBits (b : Fin 6 → Bool) : F64 := ∑ j, (if b j then basisE j else 0)

/-- The six basis coordinates of a field element, as bits. -/
noncomputable def bitsOfF64 (z : F64) : Fin 6 → Bool := fun j => (basisE.repr z j) = 1

/-- Canonical encoding of a vector over `F₆₄`: six bits per symbol. -/
noncomputable def encVec {m : ℕ} (v : Fin m → F64) : Bits :=
  (List.ofFn v).flatMap fun z => List.ofFn (bitsOfF64 z)

/-- Decoding of `encVec` (missing bits read `false`). -/
noncomputable def decVec (m : ℕ) (b : Bits) : Fin m → F64 :=
  fun i => f64OfBits fun j => b.getD (6 * i + j) false

/-- Hamming weight. -/
noncomputable def wt {m : ℕ} (v : Fin m → F64) : ℕ := (Finset.univ.filter fun i => v i ≠ 0).card

/-- Every nonzero word of `C` has weight at least `d` (the distance bound `d(C) ≥ d`). -/
def DistGE {m : ℕ} (C : Submodule F64 (Fin m → F64)) (d : ℝ) : Prop :=
  ∀ v ∈ C, v ≠ 0 → d ≤ (wt v : ℝ)

/-- The dual code `C^⊥ = {w : Σ_i w_i v_i = 0 for all v ∈ C}`. -/
noncomputable def dualCode {m : ℕ} (C : Submodule F64 (Fin m → F64)) : Submodule F64 (Fin m → F64) where
  carrier := {w | ∀ v ∈ C, w ⬝ᵥ v = 0}
  add_mem' := by
    intro a b ha hb v hv
    rw [add_dotProduct, ha v hv, hb v hv, add_zero]
  zero_mem' := by intro v _; simp
  smul_mem' := by
    intro c w hw v hv
    rw [smul_dotProduct, hw v hv, smul_zero]

/-- The diagonal twist `σ ∗ C = {σ ∗ v : v ∈ C}` (p.25). -/
noncomputable def twist {m : ℕ} (σ : Fin m → F64) (C : Submodule F64 (Fin m → F64)) :
    Submodule F64 (Fin m → F64) :=
  C.map (LinearMap.pi fun i => σ i • (LinearMap.proj i : (Fin m → F64) →ₗ[F64] F64))

/-- The pointwise inverse `σ^{-1}`. -/
noncomputable def invVec {m : ℕ} (σ : Fin m → F64) : Fin m → F64 := fun i => (σ i)⁻¹

/-- The number of disagreements of `c` and `y` outside the erasure set `E`. -/
noncomputable def errs {m : ℕ} (c y : Fin m → F64) (E : Finset (Fin m)) : ℕ :=
  (Finset.univ.filter fun i => i ∉ E ∧ c i ≠ y i).card

/-- Admissible lengths `m_j = ⌊100 N_j / 101⌋`, `N_j = 56 · 8^j` (p.25; Fact 5, p.16). -/
def admLen (j : ℕ) : ℕ := 100 * (56 * 8 ^ j) / 101

/-- `m` is an admissible length `m_j`, `j ≥ 1`. -/
def IsAdmissible (m : ℕ) : Prop := ∃ j, 1 ≤ j ∧ m = admLen j

theorem exists_admLen_ge (a : ℕ) : ∃ i, max 443 a ≤ admLen (i + 1) := by
  refine ⟨max 443 a, ?_⟩
  have h1 : max 443 a < 8 ^ (max 443 a + 1) :=
    lt_trans (Nat.lt_succ_self _) (Nat.lt_pow_self (by norm_num))
  have h2 : 8 ^ (max 443 a + 1) ≤ admLen (max 443 a + 1) := by
    unfold admLen
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have hp := pow_pos (by norm_num : (0:ℕ) < 8) (max 443 a + 1)
    nlinarith
  omega

/-- `Next(a)`, the first admissible length at least `max{443, a}` (p.25). -/
def Next (a : ℕ) : ℕ := admLen (Nat.find (exists_admLen_ge a) + 1)

/-- Canonical bit encoding of a finite set of positions (its sorted elements). -/
def encFinset {m : ℕ} (E : Finset (Fin m)) : Bits :=
  pack ((E.sort (· ≤ ·)).map fun i => encNat i.val)

/-- A string function computable by a Turing machine in polynomial time (Mathlib's
`Turing.TM2ComputableInPolyTime`, identity encodings over the alphabet `Bool`). -/
def PolyTimeBits (f : Bits → Bits) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime (id : Bits → List Bool) (id : Bits → List Bool) f)

/-- The code interface of decision D15: for each length `m` and secret capacity `q`, the codes
`B = D` and `A`, their secret maps, affine parametrizations of the secret fibers, the decoder of
Lemma 6 for the twisted code `A^σ`, and erasure extension into `D` and `A^σ`. -/
structure CodeFamily where
  /-- The code `B = D = ev_P L(G)`. -/
  B : (m q : ℕ) → Submodule F64 (Fin m → F64)
  /-- The code `A = ev_P L(2G)`. -/
  A : (m q : ℕ) → Submodule F64 (Fin m → F64)
  /-- The secret map of `B = D` (evaluation at `Q₁, …, Q_q`). -/
  secB : (m q : ℕ) → (Fin m → F64) →ₗ[F64] (Fin q → F64)
  /-- The secret map of `A`. -/
  secA : (m q : ℕ) → (Fin m → F64) →ₗ[F64] (Fin q → F64)
  /-- Dimension of the secret fibers of `B`. -/
  dimB : ℕ → ℕ → ℕ
  /-- Dimension of the secret fibers of `A`. -/
  dimA : ℕ → ℕ → ℕ
  /-- Parametrization of the fiber `B_u` by free coefficients. -/
  paramB : (m q : ℕ) → (Fin q → F64) → (Fin (dimB m q) → F64) → (Fin m → F64)
  /-- Parametrization of the fiber `A_u` by free coefficients. -/
  paramA : (m q : ℕ) → (Fin q → F64) → (Fin (dimA m q) → F64) → (Fin m → F64)
  /-- The decoder of Lemma 6 for `A^σ` with erasures `E` and error budget `T`. -/
  decodeA : (m q : ℕ) → (Fin m → F64) → Finset (Fin m) → ℕ → (Fin m → F64) →
    Option (Fin m → F64)
  /-- Extension into `D = B` of a word known outside the erasures `E`. -/
  extB : (m q : ℕ) → Finset (Fin m) → (Fin m → F64) → Option (Fin m → F64)
  /-- Extension into `A^σ` of a word known outside the erasures `E`. -/
  extA : (m q : ℕ) → (Fin m → F64) → Finset (Fin m) → (Fin m → F64) → Option (Fin m → F64)

namespace CodeFamily

open Classical in
/-- The properties of Lemmas 5 and 6 (decision D15), for every admissible `m` and
`1 ≤ q ≤ ⌊m/100⌋`. -/
def Spec (C : CodeFamily) : Prop :=
  ∀ m q : ℕ, IsAdmissible m → 1 ≤ q → q ≤ m / 100 →
    -- Lemma 5: `B ∗ D ⊆ A` and `sec(b ∗ d) = sec(b) ∗ sec(d)`
    (∀ b ∈ C.B m q, ∀ d ∈ C.B m q, b * d ∈ C.A m q ∧
        C.secA m q (b * d) = C.secB m q b * C.secB m q d) ∧
    -- Lemma 5: the secret maps are onto
    (∀ u : Fin q → F64, (∃ b ∈ C.B m q, C.secB m q b = u) ∧ (∃ a ∈ C.A m q, C.secA m q a = u)) ∧
    -- Lemma 5 (and its proof): distances
    DistGE (dualCode (C.B m q ⊓ LinearMap.ker (C.secB m q))) (0.048 * m + 1) ∧
    DistGE (C.B m q) (0.65 * m) ∧ DistGE (C.A m q) (0.30 * m) ∧
    -- uniform sampling in a secret fiber
    (∀ u, Function.Injective (C.paramB m q u) ∧
        Set.range (C.paramB m q u) = {b | b ∈ C.B m q ∧ C.secB m q b = u}) ∧
    (∀ u, Function.Injective (C.paramA m q u) ∧
        Set.range (C.paramA m q u) = {a | a ∈ C.A m q ∧ C.secA m q a = u}) ∧
    -- Lemma 6: the decoder for `A^σ`
    (∀ σ : Fin m → F64, (∀ i, σ i ≠ 0) → ∀ (E : Finset (Fin m)) (T : ℕ) (y : Fin m → F64),
      (∀ c, C.decodeA m q σ E T y = some c → c ∈ twist σ (C.A m q) ∧ errs c y E ≤ T) ∧
      ((2 * T + E.card : ℝ) ≤ 0.15 * m → ∀ c ∈ twist σ (C.A m q), errs c y E ≤ T →
        C.decodeA m q σ E T y = some c)) ∧
    -- recovery of a codeword from all but the erased coordinates
    (∀ (E : Finset (Fin m)) (y : Fin m → F64),
      (∀ c, C.extB m q E y = some c → c ∈ C.B m q ∧ ∀ i ∉ E, c i = y i) ∧
      ((∃ c ∈ C.B m q, ∀ i ∉ E, c i = y i) → (C.extB m q E y).isSome)) ∧
    (∀ σ : Fin m → F64, (∀ i, σ i ≠ 0) → ∀ (E : Finset (Fin m)) (y : Fin m → F64),
      (∀ c, C.extA m q σ E y = some c → c ∈ twist σ (C.A m q) ∧ ∀ i ∉ E, c i = y i) ∧
      ((∃ c ∈ twist σ (C.A m q), ∀ i ∉ E, c i = y i) → (C.extA m q σ E y).isSome))
  ∧
  -- Lemma 5, last sentence, and Lemma 6: the code operations are uniformly polynomial-time
  -- (inputs and outputs in the canonical encodings, the parameters `m, q` in binary)
  PolyTimeBits (fun x => match unpack x with
    | [m, q, σ, v] => [decide (decVec (bitsNat m) v ∈ twist (decVec (bitsNat m) σ)
        (C.B (bitsNat m) (bitsNat q)))]
    | _ => []) ∧
  PolyTimeBits (fun x => match unpack x with
    | [m, q, σ, v] => [decide (decVec (bitsNat m) v ∈ twist (decVec (bitsNat m) σ)
        (C.A (bitsNat m) (bitsNat q)))]
    | _ => []) ∧
  PolyTimeBits (fun x => match unpack x with
    | [m, q, v] => encVec (C.secB (bitsNat m) (bitsNat q) (decVec (bitsNat m) v))
    | _ => []) ∧
  PolyTimeBits (fun x => match unpack x with
    | [m, q, v] => encVec (C.secA (bitsNat m) (bitsNat q) (decVec (bitsNat m) v))
    | _ => []) ∧
  PolyTimeBits (fun x => match unpack x with
    | [m, q, u, c] => encVec (C.paramB (bitsNat m) (bitsNat q) (decVec (bitsNat q) u)
        (decVec (C.dimB (bitsNat m) (bitsNat q)) c))
    | _ => []) ∧
  PolyTimeBits (fun x => match unpack x with
    | [m, q, u, c] => encVec (C.paramA (bitsNat m) (bitsNat q) (decVec (bitsNat q) u)
        (decVec (C.dimA (bitsNat m) (bitsNat q)) c))
    | _ => []) ∧
  PolyTimeBits (fun x => match unpack x with
    | [m, q, σ, e, t, y] =>
      match C.decodeA (bitsNat m) (bitsNat q) (decVec (bitsNat m) σ)
          (Finset.univ.filter fun i : Fin (bitsNat m) => e.getD i false) (bitsNat t)
          (decVec (bitsNat m) y) with
      | some c => true :: encVec c
      | none => [false]
    | _ => []) ∧
  PolyTimeBits (fun x => match unpack x with
    | [m, q, e, y] =>
      match C.extB (bitsNat m) (bitsNat q)
          (Finset.univ.filter fun i : Fin (bitsNat m) => e.getD i false) (decVec (bitsNat m) y) with
      | some c => true :: encVec c
      | none => [false]
    | _ => []) ∧
  PolyTimeBits (fun x => match unpack x with
    | [m, q, σ, e, y] =>
      match C.extA (bitsNat m) (bitsNat q) (decVec (bitsNat m) σ)
          (Finset.univ.filter fun i : Fin (bitsNat m) => e.getD i false) (decVec (bitsNat m) y) with
      | some c => true :: encVec c
      | none => [false]
    | _ => [])

end CodeFamily

end DIObliviousTransfer


