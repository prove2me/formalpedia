-- Prove2me | Definitions.Def_ShuffleDecoys_Hierarchy_Model
-- name    : ShuffleDecoys_Hierarchy_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:22:34.713455+00:00
-- url     : https://prove2.me/theorems/30fd3ef9-72f9-41bc-85c2-2cc13a073596
-- title:
--   The shuffle-only release, the four decoy-mechanism classes, the output histogram and the minimax leakage L_C(d, n), L_C(P, n)
-- statement:
--   A genuine message $M\sim P$ takes values in an alphabet $Y$ (for the paper's $[d]=\{1,\dots,d\}$ this is `Fin d`). A **decoy mechanism** for $n$ released entries is a Markov kernel $R$ that, given $M=m$, draws the $n-1$ decoys $H=(H_2,\dots,H_n)\in Y^{n-1}$ from $R(m)$; it never sees the prior. The pre-shuffle list is $(M,H_2,\dots,H_n)$ (`genuineFirst`), and the shuffler draws $\sigma$ uniformly from the permutations of the $n$ positions, independently of $(M,H)$, and releases
--   $$Z=(Y_{\sigma(1)},\dots,Y_{\sigma(n)}).$$
--   `shuffleExperiment P R` is the law of $(M,H,\sigma)$, `shuffleOutput` the release $Z$, `genuinePosition` the position $K=\sigma^{-1}(\text{genuine slot})$ of the genuine message in $Z$, and `shuffleLaw P R` the joint law of $(M,Z)$.
--
--   The four nested classes of mechanisms are
--   - **canonical** (`canClass`): $H_i$ i.i.d. from one blanket $Q$, independent of $M$;
--   - **heterogeneous** (`hetClass`): $H_i\sim Q_i$ mutually independent, independent of $M$;
--   - **message-oblivious** (`oblClass`): $H$ has one arbitrary joint law whatever $M$ is;
--   - **message-dependent** (`depClass`): every kernel.
--
--   With $e_m$ the unit count vector of $m$ and $S=\sum_{i=2}^n e_{H_i}$ the **decoy histogram** (`decoyHist`), `histLaw P R` is the joint law of $(M,T)$ with $T=e_M+S$, the **output histogram**; `noiseJoint P S` is the joint law of $(M,e_M+S)$ for an integer noise vector $S$ independent of $M$.
--
--   With $I_P(M;Z_A)$ the mutual information in nats (`leakage`), the optimal leakages of a class $\mathcal C$ are
--   $$L_{\mathcal C}(P,n)=\inf_{A\in\mathcal C}I_P(M;Z_A),\qquad L_{\mathcal C}(d,n)=\inf_{A\in\mathcal C}\ \sup_{P\in\Delta_d}I_P(M;Z_A),$$
--   the supremum running over the closed simplex $\Delta_d$ of all priors on $[d]$ (zero entries allowed). `Lcan`, `Lhet`, `Lobl`, `Ldep` are $L_{\mathcal C}(d,n)$ and `LcanP`, `LhetP` are $L_{\mathcal C}(P,n)$. Finally $v(P)=\max_{E\subseteq\operatorname{supp}(P)}P(E)(1-P(E))$ (`vP`).
--
--   **Formalization Note.** Decoys are indexed by `Fin (n - 1)` and the release by `Fin n` with the genuine message in slot $0$ before shuffling; the model is meant for $n\ge1$. The infimum and supremum are taken in $[0,\infty]$, where they are always the true infimum and supremum; every class is nonempty. `vP` is a real supremum over the finitely many subsets of the support (a nonempty finite family), hence the maximum.
-- source:
--   Su, Cheng, Wang, The Information-Theoretic Limits of Hiding Among Decoys in the Shuffle Model, STOC 2027 submission (manuscript sha256 445baceb…), p. 3 (shuffle convention, K), p. 4 (§1.1, the four classes), p. 5 (Eq. (1), histogram), p. 7 (Eq. (2)), p. 15 (v(P), Theorem 3.1), p. 16 (T = e_M + S)

import Mathlib
import Definitions.Def_ShuffleDecoys_Hierarchy_Info

open scoped ENNReal

namespace ShuffleDecoys.Hierarchy

/-!
# The shuffle-only release, the four decoy classes and the minimax leakage

Su, Cheng, Wang, *The Information-Theoretic Limits of Hiding Among Decoys in the Shuffle Model*,
STOC 2027 submission, pp. 3–5 (§1.1, Eq. (1)), p. 7 (Eq. (2)), p. 15 (`v(P)`).

* The genuine message `M ∼ P` takes values in an alphabet `Y` (`Fin d` for `[d]`); the `n − 1`
  decoys `H = (H₂, …, Hₙ)` are indexed by `Fin (n - 1)` and take values in `Y` too.
* A mechanism is a decoy kernel `R : Y → PMF (Fin (n - 1) → Y)`, `R m = Law(H | M = m)`; it never
  sees the prior. The four classes are sets of kernels.
* `Y = (M, H₂, …, Hₙ)` is the genuine-first list (`genuineFirst`, position `0` holds `M`), and
  the release is `Z = (Y_{σ(1)}, …, Y_{σ(n)})`, `Z i = Y (σ i)`, for `σ` uniform on the
  permutations of `Fin n`, independent of `(M, H)`.
* The model is meant for `n ≥ 1` (the release contains the genuine message).
-/

/-- A decoy mechanism for `n` released entries: a Markov kernel from the genuine message to the
joint law of its `n − 1` decoys. -/
abbrev DecoyKernel (Y : Type*) (n : ℕ) := Y → PMF (Fin (n - 1) → Y)

/-- The pre-shuffle list `(M, H₂, …, Hₙ)`: entry `0` is the genuine message `m`, entry `i ≥ 1` is
the decoy `h (i − 1)`. -/
def genuineFirst {Y : Type*} {n : ℕ} (m : Y) (h : Fin (n - 1) → Y) (i : Fin n) : Y :=
  if hi : i.val = 0 then m else h ⟨i.val - 1, by omega⟩

/-- The full shuffle experiment: the law of `(M, H, σ)` with `M ∼ P`, `H ∼ R M`, and `σ` uniform on
the permutations of `Fin n`, independent of `(M, H)`. -/
noncomputable def shuffleExperiment {Y : Type*} {n : ℕ} (P : PMF Y) (R : DecoyKernel Y n) :
    PMF (Y × (Fin (n - 1) → Y) × Equiv.Perm (Fin n)) :=
  P.bind fun m => (R m).bind fun h =>
    (PMF.uniformOfFintype (Equiv.Perm (Fin n))).map fun σ => (m, h, σ)

/-- The released sequence `Z = (Y_{σ(i)})ᵢ` of an outcome `(m, h, σ)` of the experiment. -/
def shuffleOutput {Y : Type*} {n : ℕ} (ω : Y × (Fin (n - 1) → Y) × Equiv.Perm (Fin n)) :
    Fin n → Y :=
  fun i => genuineFirst ω.1 ω.2.1 (ω.2.2 i)

/-- The position `K = σ⁻¹(genuine slot)` of the genuine message in the release. -/
def genuinePosition {Y : Type*} {n : ℕ} (hn : 1 ≤ n)
    (ω : Y × (Fin (n - 1) → Y) × Equiv.Perm (Fin n)) : Fin n :=
  ω.2.2.symm ⟨0, hn⟩

/-- The joint law of `(M, Z)`: the genuine message and the shuffled release. -/
noncomputable def shuffleLaw {Y : Type*} {n : ℕ} (P : PMF Y) (R : DecoyKernel Y n) :
    PMF (Y × (Fin n → Y)) :=
  (shuffleExperiment P R).map fun ω => (ω.1, shuffleOutput ω)

/-- The unit count vector `e_m ∈ ℤ^Y`. -/
def unitVec {Y : Type*} [DecidableEq Y] (m : Y) : Y → ℤ :=
  Pi.single m 1

/-- The decoy histogram `S = Σᵢ e_{Hᵢ}`: `S y` counts the decoys equal to `y`. -/
def decoyHist {Y : Type*} [DecidableEq Y] {k : ℕ} (h : Fin k → Y) : Y → ℤ :=
  fun y => ((Finset.univ.filter fun i => h i = y).card : ℤ)

/-- The joint law of `(M, T)` with `T = e_M + S` the output histogram (Eq. (1)), computed from the
genuine message and its decoys (no shuffle involved). -/
noncomputable def histLaw {Y : Type*} [DecidableEq Y] {n : ℕ} (P : PMF Y)
    (R : DecoyKernel Y n) : PMF (Y × (Y → ℤ)) :=
  channelJoint P fun m => (R m).map fun h => unitVec m + decoyHist h

/-- The joint law of `(M, T)` with `T = e_M + S`, for integer noise `S ∼ σ` independent of
`M ∼ P` (§3.2). -/
noncomputable def noiseJoint {Y : Type*} [DecidableEq Y] (P : PMF Y) (σ : PMF (Y → ℤ)) :
    PMF (Y × (Y → ℤ)) :=
  channelJoint P fun m => σ.map fun s => unitVec m + s

/-- Message-dependent decoys: every kernel. -/
def depClass (Y : Type*) (n : ℕ) : Set (DecoyKernel Y n) := Set.univ

/-- Message-oblivious decoys: the decoy vector has one joint law whatever the message (`H ⊥ M`). -/
def oblClass (Y : Type*) (n : ℕ) : Set (DecoyKernel Y n) :=
  {R | ∀ m m', R m = R m'}

/-- Heterogeneous decoys: `Hᵢ ∼ Qᵢ` mutually independent and independent of `M`. -/
def hetClass (Y : Type*) (n : ℕ) : Set (DecoyKernel Y n) :=
  {R | ∃ Q : Fin (n - 1) → PMF Y, ∀ m h, R m h = ∏ i, Q i (h i)}

/-- Canonical decoys: `Hᵢ` i.i.d. from one blanket `Q`, independent of `M`. -/
def canClass (Y : Type*) (n : ℕ) : Set (DecoyKernel Y n) :=
  {R | ∃ Q : PMF Y, ∀ m h, R m h = ∏ i, Q (h i)}

/-- The leakage `I_P(M; Z_A)` in nats of mechanism `R` under prior `P`. -/
noncomputable def leakage {Y : Type*} {n : ℕ} (P : PMF Y) (R : DecoyKernel Y n) : ℝ≥0∞ :=
  mutualInfo (shuffleLaw P R)

/-- Prior-specific optimal leakage `L_C(P, n) = inf_{A ∈ C} I_P(M; Z_A)` (Eq. (2)), in `[0, ∞]`. -/
noncomputable def priorLeak {Y : Type*} {n : ℕ} (C : Set (DecoyKernel Y n)) (P : PMF Y) : ℝ≥0∞ :=
  ⨅ R ∈ C, leakage P R

/-- Minimax leakage `L_C = inf_{A ∈ C} sup_{P} I_P(M; Z_A)` (Eq. (2)), the supremum over every
prior on `Y` (the closed simplex), in `[0, ∞]`. -/
noncomputable def minimaxLeak {Y : Type*} {n : ℕ} (C : Set (DecoyKernel Y n)) : ℝ≥0∞ :=
  ⨅ R ∈ C, ⨆ P : PMF Y, leakage P R

/-- `L_can(d, n)`. -/
noncomputable def Lcan (d n : ℕ) : ℝ≥0∞ := minimaxLeak (canClass (Fin d) n)
/-- `L_het(d, n)`. -/
noncomputable def Lhet (d n : ℕ) : ℝ≥0∞ := minimaxLeak (hetClass (Fin d) n)
/-- `L_obl(d, n)`. -/
noncomputable def Lobl (d n : ℕ) : ℝ≥0∞ := minimaxLeak (oblClass (Fin d) n)
/-- `L_dep(d, n)`. -/
noncomputable def Ldep (d n : ℕ) : ℝ≥0∞ := minimaxLeak (depClass (Fin d) n)

/-- `L_can(P, n)`. -/
noncomputable def LcanP {Y : Type*} (P : PMF Y) (n : ℕ) : ℝ≥0∞ := priorLeak (canClass Y n) P
/-- `L_het(P, n)`. -/
noncomputable def LhetP {Y : Type*} (P : PMF Y) (n : ℕ) : ℝ≥0∞ := priorLeak (hetClass Y n) P

/-- `v(P) = max_{E ⊆ supp(P)} P(E)(1 − P(E))` (Theorem 3.1), a maximum over finitely many sets. -/
noncomputable def vP {Y : Type*} [Fintype Y] (P : PMF Y) : ℝ :=
  ⨆ E : {E : Finset Y // ∀ y ∈ E, P y ≠ 0},
    (∑ y ∈ E.1, (P y).toReal) * (1 - ∑ y ∈ E.1, (P y).toReal)

end ShuffleDecoys.Hierarchy


