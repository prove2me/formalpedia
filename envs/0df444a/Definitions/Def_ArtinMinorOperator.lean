-- Prove2me | Definitions.Def_ArtinMinorOperator
-- name    : ArtinMinorOperator
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T00:20:41.462866+00:00
-- url     : https://prove2.me/theorems/3aa52dad-d798-4d53-839a-29b3d0f51089
-- title:
--   The operator of [21] §§3.2–3.3: physical states, goodness, the row operation T, A = GSTSG, and its moment and pairings at the dyad 2^k
-- statement:
--   The objects through which the coprime minor-arc part of Lemma 10.2's proof is bounded. They build on the bundles `Def_ArtinSieve`, `Def_ArtinMarkedSquare` and `Def_ArtinMinorSquare`.
--
--   * The good-position tests `GoodTestOne`, `GoodTestTwo` and `IsGoodRatio`.
--   * The parameters `padCount` ($J$), `momentPower` ($R$) and `rootRatio` ($r_P$).
--   * The positions `posBox` and the physical states `stateSet` / `PhysState`: a position with ordered lists of group primes.
--   * The operators: the goodness projection `goodProj` ($G$), the slot symmetrization `slotSym` ($S$), the row operation `rowOp` ($T$, with the kernel (3.15)) and `opA` ($A = GSTSG$).
--   * The moment `momentSum`, the endpoint vector `endpointVec` and the pairing `opPairing`.
--   * Their values at the pad dyad $2^k$: `dyadMoment`, `dyadPairingSTS` and `dyadPairingA`.
--
--   Source: [21] = OpenAI, *The Poisson–Dirichlet law for prime predecessors* (2026), pp. 11–14, §§3.2–3.3.
-- source:
--   OpenAI, The Poisson-Dirichlet law for prime predecessors, OpenAI Math Release preprint, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/paper.pdf (Apache-2.0), p. 11–14, §§3.2–3.3 (physical states, goodness, S, T, A = GSTSG, moment and pairings at dyads)

import Mathlib
import Definitions.Def_ArtinSieve
import Definitions.Def_ArtinMarkedSquare
import Definitions.Def_ArtinMinorSquare

/-! # The operator of [21] §§3.2–3.3

The physical states, the good-position tests, the slot symmetrization `S`, the goodness projection
`G`, the row operation `T` with kernel [21] (3.15), `A = G S T S G`, the moment
`∑_P ⟨u_P, (AA*)^R u_P⟩` of (3.19)/(4.1), and the endpoint vectors `f = g` of (3.16).

Conventions. Lists have `J + 1` slots per group: slots `0, …, J − 1` are the pads (copied along an
edge, product `D`), slot `J` (`Fin.last J`) is the unshared label. The Hilbert-space measure
`∏ Vᵢ^{-(J+1)}` × counting is constant on states, so `σ`-adjoints are conjugate transposes; the
constant `stateNorm` is carried explicitly in `momentSum` and `opPairing`. The auxiliary damping
parameter of (3.15) is fixed to `q = 1/4`, so `q^{(ω(P₁)−KM)/2} = (1/2)^{ω(P₁)−KM}`. Test (i) and
test (ii) use all omission products. -/

namespace ArtinPrimitiveRoots

open Real

/-! ## Good positions ([21] §3.2) -/

/-- `‖t‖_{ℝ/ℤ} = |t − round t|`, the distance to the nearest integer. -/
noncomputable def circNorm (t : ℝ) : ℝ := |t - round t|


/-- The omission product `D`: omit the label `ℓ i (o i)` from each group `i`, multiply the rest. -/
def omitProd {K M : ℕ} (ℓ : Fin K → Fin M → ℕ) (o : Fin K → Fin M) : ℕ :=
  ∏ i, ∏ j ∈ Finset.univ.erase (o i), ℓ i j

/-- **Test (i)** of [21] §3.2: for no omission product `D` and no `1 ≤ l ≤ Y^{0.2}` is
`‖l D r‖ ≤ Y^{-0.7}`. -/
def GoodTestOne {K M : ℕ} (Y : ℝ) (ℓ : Fin K → Fin M → ℕ) (r : ℝ) : Prop :=
  ∀ o : Fin K → Fin M, ∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ Y ^ (0.2 : ℝ) →
    Y ^ (-0.7 : ℝ) < circNorm (((l * omitProd ℓ o : ℕ) : ℝ) * r)

/-- The fresh draws of test (ii): one prime of `𝒫ᵢ` for each group `i ∉ I` (the entry `1` for
`i ∈ I`). -/
noncomputable def freshTuples (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (I : Finset (Fin K)) :
    Finset (Fin K → ℕ) :=
  Fintype.piFinset fun i => if i ∈ I then {1} else primeGroup x (a i)

/-- The law `μ = ⊗_{i ∉ I} μᵢ`, `μᵢ(p) = 1/(p Vᵢ)`, of the fresh draws. -/
noncomputable def freshWeight (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (I : Finset (Fin K))
    (T : Fin K → ℕ) : ℝ :=
  ∏ i, if i ∈ I then 1 else 1 / ((T i : ℝ) * groupReciprocalSum x (a i))

/-- The selections `Z`: one prime of `𝒫ᵢ` for each `i ∈ I ∖ {i₀}` (the entry `1` elsewhere). -/
noncomputable def zTuples (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (I : Finset (Fin K)) (i₀ : Fin K) :
    Finset (Fin K → ℕ) :=
  Fintype.piFinset fun i => if i ∈ I ∧ i ≠ i₀ then primeGroup x (a i) else {1}

/-- Failure of the phase separation in test (ii) for the fresh draw `T`: two distinct integers
`DZ ≠ D′Z′` with `‖(DZ − D′Z′) T_f r‖ < 100 exp(−L^{a_{i₀}})`. -/
def SepFails (x : ℝ) {K M : ℕ} (a : Fin K → ℝ) (ℓ : Fin K → Fin M → ℕ) (I : Finset (Fin K))
    (i₀ : Fin K) (T : Fin K → ℕ) (r : ℝ) : Prop :=
  ∃ o o' : Fin K → Fin M, ∃ Z Z' : Fin K → ℕ, Z ∈ zTuples x a I i₀ ∧ Z' ∈ zTuples x a I i₀ ∧
    omitProd ℓ o * ∏ i, Z i ≠ omitProd ℓ o' * ∏ i, Z' i ∧
    circNorm (((((omitProd ℓ o * ∏ i, Z i : ℕ) : ℤ) - ((omitProd ℓ o' * ∏ i, Z' i : ℕ) : ℤ)) *
      ((∏ i, T i : ℕ) : ℤ) : ℤ) * r) < 100 * exp (-(log x ^ a i₀))

open Classical in
/-- **Test (ii)** of [21] §3.2: for every nonempty `I` with `i* = max I`, the `μ`-probability of
fresh draws for which the phase separation fails is at most `exp(−L^{a_{i*}}/4)`. -/
def GoodTestTwo (x : ℝ) {K M : ℕ} (a : Fin K → ℝ) (ℓ : Fin K → Fin M → ℕ) (r : ℝ) : Prop :=
  ∀ I : Finset (Fin K), ∀ hI : I.Nonempty,
    ∑ T ∈ freshTuples x a I,
      freshWeight x a I T * (if SepFails x a ℓ I (I.max' hI) T r then 1 else 0) ≤
      exp (-(log x ^ a (I.max' hI)) / 4)

/-- A good ratio: both tests hold. -/
def IsGoodRatio (x Y : ℝ) {K M : ℕ} (a : Fin K → ℝ) (ℓ : Fin K → Fin M → ℕ) (r : ℝ) : Prop :=
  GoodTestOne Y ℓ r ∧ GoodTestTwo x a ℓ r


/-! ## Parameters, positions and physical states -/

/-- `J = ⌊L^{0.01}⌋`, the number of pads per group (lists have `M = J + 1` slots), (3.12). -/
noncomputable def padCount (x : ℝ) : ℕ := ⌊log x ^ (0.01 : ℝ)⌋₊

/-- `R = ⌈L^{0.5}/2⌉`; the moment is that of `(AA*)^R`, a closed path of `N = 2R` edges, (3.12). -/
noncomputable def momentPower (x : ℝ) : ℕ := ⌈log x ^ (0.5 : ℝ) / 2⌉₊

/-- `r_P = c/u mod 1`, where `(u c; v d)` is the completion of the primitive `(u, v)` with
`ud − vc = 1` and `0 ≤ c < u`, i.e. `c ≡ −v⁻¹ (mod u)`, (3.22). -/
noncomputable def rootRatio (u v : ℕ) : ℝ := ((-(v : ZMod u)⁻¹ : ZMod u).val : ℝ) / u

/-- The primitive positions in `Ω = [U, 16U] × [V, 2V]`, (3.13). -/
noncomputable def posBox (U V : ℝ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc ⌈U⌉₊ ⌊16 * U⌋₊) ×ˢ (Finset.Icc ⌈V⌉₊ ⌊2 * V⌋₊)).filter
    fun P => Nat.Coprime P.1 P.2

/-- Candidate lists: `J + 1` primes of `𝒫ᵢ` in each group `i`. -/
noncomputable def listCands (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (J : ℕ) :
    Finset (Fin K → Fin (J + 1) → ℕ) :=
  Fintype.piFinset fun i => Fintype.piFinset fun _ => primeGroup x (a i)

open Classical in
/-- The physical states: a primitive position `P ∈ Ω` and, in each group, an ordered list of
`J + 1` distinct primes of the group, all dividing `P₁`, (3.14). -/
noncomputable def stateSet (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (J : ℕ) (U V : ℝ) :
    Finset ((ℕ × ℕ) × (Fin K → Fin (J + 1) → ℕ)) :=
  (posBox U V ×ˢ listCands x a J).filter fun s =>
    (∀ i, Function.Injective (s.2 i)) ∧ ∀ i j, s.2 i j ∣ s.1.1

/-- The type of physical states. -/
abbrev PhysState (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (J : ℕ) (U V : ℝ) :=
  {s // s ∈ stateSet x a J U V}

/-- The pad product `D` (slots `0, …, J − 1`). -/
def padProd {K J : ℕ} (ℓ : Fin K → Fin (J + 1) → ℕ) : ℕ := ∏ i, ∏ j : Fin J, ℓ i j.castSucc

/-- The product of the unshared (last) labels. -/
def lastProd {K J : ℕ} (ℓ : Fin K → Fin (J + 1) → ℕ) : ℕ := ∏ i, ℓ i (Fin.last J)

/-- `ω(n) − K(J+1)`: the number of group primes dividing `n` beyond the listed ones. -/
noncomputable def excessOmega (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (J n : ℕ) : ℕ :=
  markOmega x a n - K * (J + 1)

/-- The state measure `σ = ∏ᵢ Vᵢ^{-(J+1)}`, (3.14). -/
noncomputable def stateNorm (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (J : ℕ) : ℝ :=
  ∏ i, (groupReciprocalSum x (a i))⁻¹ ^ (J + 1)

/-! ## The operators -/

open Classical in
/-- The goodness projection `G`. -/
noncomputable def goodProj (x Y : ℝ) {K : ℕ} (a : Fin K → ℝ) (J : ℕ) (U V : ℝ) :
    Matrix (PhysState x a J U V) (PhysState x a J U V) ℂ :=
  Matrix.diagonal fun s =>
    if IsGoodRatio x Y a s.1.2 (rootRatio s.1.1.1 s.1.1.2) then 1 else 0

open Classical in
/-- The slot symmetrization `S`: the average over the reorderings of the lists, i.e. over the
states with the same position and the same set of labels in each group (the orbit of the slot
permutations, of size `(J+1)!^K`): `S(s, s') = 1/#orbit(s)` if `s'` is in the orbit of `s`. -/
noncomputable def slotSym (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (J : ℕ) (U V : ℝ) :
    Matrix (PhysState x a J U V) (PhysState x a J U V) ℂ :=
  fun s s' => if s.1.1 = s'.1.1 ∧ ∀ i, Set.range (s'.1.2 i) = Set.range (s.1.2 i) then
    ((Finset.univ.filter fun t : PhysState x a J U V =>
      t.1.1 = s.1.1 ∧ ∀ i, Set.range (t.1.2 i) = Set.range (s.1.2 i)).card : ℂ)⁻¹ else 0

open Classical in
/-- The row operation `T` of [21] §3.2 with the kernel (3.15): copy the pads, replace the last
label of every group by a new label not in the source list (the cross-edge ban), require
`D ∈ [d₀, 2d₀)`, and use the multiplier
`∏Vᵢ⁻¹ (d₀/D) η(b/Y) η(a/Y) ψ(t/Y) [1_{t=b−a} − ∫_𝔐 e(θ(t−b+a)) dθ] (1/2)^{ω(P₁)−KM+ω(Q₁)−KM}`
with `b`, `a` the source and target last products and `t = det(P, Q)/D`; the bracket times
`ψ(t/Y)` is `minorKernel x A₀ Y t a b`. -/
noncomputable def rowOp (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (A₀ Y : ℝ) (J d₀ : ℕ) (U V : ℝ) :
    Matrix (PhysState x a J U V) (PhysState x a J U V) ℂ :=
  fun s s' =>
    if (∀ i (j : Fin J), s'.1.2 i j.castSucc = s.1.2 i j.castSucc) ∧
        (∀ i, s'.1.2 i (Fin.last J) ∉ Set.range (s.1.2 i)) ∧
        d₀ ≤ padProd s.1.2 ∧ padProd s.1.2 < 2 * d₀ then
      (((∏ i, (groupReciprocalSum x (a i))⁻¹) * ((d₀ : ℝ) / padProd s.1.2) *
          dyadicBump ((lastProd s.1.2 : ℝ) / Y) * dyadicBump ((lastProd s'.1.2 : ℝ) / Y) *
          (1 / 2 : ℝ) ^ (excessOmega x a J s.1.1.1 + excessOmega x a J s'.1.1.1) : ℝ) : ℂ) *
        minorKernel x A₀ Y
          (((s.1.1.1 : ℤ) * s'.1.1.2 - (s.1.1.2 : ℤ) * s'.1.1.1) / (padProd s.1.2 : ℤ))
          (lastProd s'.1.2) (lastProd s.1.2)
    else 0

/-- `A = G S T S G`. -/
noncomputable def opA (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (A₀ Y : ℝ) (J d₀ : ℕ) (U V : ℝ) :
    Matrix (PhysState x a J U V) (PhysState x a J U V) ℂ :=
  goodProj x Y a J U V * slotSym x a J U V * rowOp x a A₀ Y J d₀ U V * slotSym x a J U V *
    goodProj x Y a J U V

open Classical in
/-- The moment `∑_{P ∈ Ω primitive} ⟨u_P, (AA*)^R u_P⟩_σ`, `u_P` the indicator of the states at
position `P`, (3.19). -/
noncomputable def momentSum (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (A₀ Y : ℝ) (J R d₀ : ℕ)
    (U V : ℝ) : ℂ :=
  (stateNorm x a J : ℂ) * ∑ s : PhysState x a J U V, ∑ s' : PhysState x a J U V,
    if s.1.1 = s'.1.1 then
      ((opA x a A₀ Y J d₀ U V * (opA x a A₀ Y J d₀ U V).conjTranspose) ^ R) s s' else 0

open Classical in
/-- The endpoint vector of (3.16), `f = g`: if the complete group part `G(P₁)` of `P₁` is
squarefree with exactly `J + 1` primes from each group, the value `conj(α_{P₁/G(P₁)}) β_{P₂}`;
otherwise `0`. It depends on the state only through its position. -/
noncomputable def endpointVec (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (J : ℕ) (U V : ℝ)
    (α β : ℕ → ℂ) (s : PhysState x a J U V) : ℂ :=
  if (∀ i, groupOmega x (a i) s.1.1.1 = J + 1) ∧ Squarefree (groupPart x a s.1.1.1) then
    (starRingEnd ℂ) (α (s.1.1.1 / groupPart x a s.1.1.1)) * β s.1.1.2 else 0

/-- The pairing `⟨f, B f⟩_σ` with the endpoint vector. -/
noncomputable def opPairing (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (J : ℕ) (U V : ℝ) (α β : ℕ → ℂ)
    (B : Matrix (PhysState x a J U V) (PhysState x a J U V) ℂ) : ℂ :=
  (stateNorm x a J : ℂ) * ∑ s, ∑ s', (starRingEnd ℂ) (endpointVec x a J U V α β s) * B s s' *
    endpointVec x a J U V α β s'

/-! ## The objects at the dyad `d₀ = 2^k`, with `J = padCount x`, `R = momentPower x`,
`U = 2^k Y H_m`, `V = H_n` -/

/-- The moment at dyad `2^k`. -/
noncomputable def dyadMoment (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (A₀ Y Hm Hn : ℝ) (k : ℕ) : ℂ :=
  momentSum x a A₀ Y (padCount x) (momentPower x) (2 ^ k) (2 ^ k * Y * Hm) Hn

/-- The pairing `⟨f, S T S f⟩_σ` (no goodness projections) at dyad `2^k`. -/
noncomputable def dyadPairingSTS (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (A₀ Y Hm Hn : ℝ)
    (α β : ℕ → ℂ) (k : ℕ) : ℂ :=
  opPairing x a (padCount x) (2 ^ k * Y * Hm) Hn α β
    (slotSym x a (padCount x) (2 ^ k * Y * Hm) Hn *
      rowOp x a A₀ Y (padCount x) (2 ^ k) (2 ^ k * Y * Hm) Hn *
      slotSym x a (padCount x) (2 ^ k * Y * Hm) Hn)

/-- The pairing `⟨f, A f⟩_σ` at dyad `2^k`. -/
noncomputable def dyadPairingA (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (A₀ Y Hm Hn : ℝ)
    (α β : ℕ → ℂ) (k : ℕ) : ℂ :=
  opPairing x a (padCount x) (2 ^ k * Y * Hm) Hn α β
    (opA x a A₀ Y (padCount x) (2 ^ k) (2 ^ k * Y * Hm) Hn)

end ArtinPrimitiveRoots


