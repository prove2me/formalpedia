-- Prove2me | Definitions.Def_GuanQinQDP_Restricted_Measurements
-- name    : GuanQinQDP_Restricted_Measurements
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:41:36.54947+00:00
-- url     : https://prove2.me/theorems/10b30b46-5b54-4b86-ac2d-92dfa198d0a3
-- title:
--   Measurement classes Product, LOCC, SEP, PPT$(i)$, PPT and ALL on $n$ output sites
-- statement:
--   The output has one site per register, $K=\bigotimes_{j=1}^nK_j$, each site $\mathbb C^d$. An **event** of a POVM $\{M_z\}_{z\in\Omega}$ is an effect $\sum_{z\in S}M_z$ with $S\subseteq\Omega$. The event set $\mathcal E(\mathcal M)$ of a class $\mathcal M$ collects the events of the POVMs of that class (§2.2).
--
--   1. **Product.** Each site $j$ measures a local POVM $\{P_{j,z}\}_z$, and the tuple of outcomes is classically post-processed. The events are $\sum_z f(z)\,P_{1,z_1}\otimes\cdots\otimes P_{n,z_n}$ with $0\le f\le1$.
--   2. **LOCC.** The events of $n$-party protocols of local operations and classical communication with local memories of any finite dimension. In each round one party applies a local instrument with Kraus operators $K_a$, $\sum_aK_a^\dagger K_a=I$, and broadcasts the outcome; the rest of the protocol may depend on it. A protocol that stops accepts with event $I$ or rejects with event $0$. The event of a round is $\sum_a(I\otimes K_a)^\dagger E_a(I\otimes K_a)$. The class is the closure of the events of all finite-round protocols.
--   3. **SEP.** Effects $M$ such that both $M$ and $I-M$ are fully separable: finite sums of products of positive semidefinite operators on the $n$ sites.
--   4. **PPT$(i)$ and PPT.** With $T_i$ the partial transpose on site $i$ in the computational basis,
--   $$\mathcal E^{(i)}_{\mathrm{PPT}}=\{M:0\preceq M\preceq I,\ 0\preceq M^{T_i}\preceq I\},\qquad \mathcal E_{\mathrm{PPT}}=\bigcap_{i=1}^n\mathcal E^{(i)}_{\mathrm{PPT}}.$$
--   Only single-site cuts are used, not every bipartition.
--   5. **ALL.** Every effect.
--
--   Thus $\mathcal E_{\mathrm{Product}}\subseteq\mathcal E_{\mathrm{LOCC}}\subseteq\mathcal E_{\mathrm{SEP}}\subseteq\mathcal E_{\mathrm{PPT}}\subseteq\mathcal E^{(i)}_{\mathrm{PPT}}\subseteq\mathcal E_{\mathrm{ALL}}$. These are the observers of the maximum rule.
--
--   **Formalization Note** An operator on $n$ sites is a matrix indexed by `Fin n → Fin d`. In the LOCC predicate the local dimensions are tracked as a vector `d : Fin n → ℕ`, so a party can add ancillas or discard subsystems. Finite-round LOCC is the inductive predicate `IsLOCCEventFin`. `loccEvents` is its closure in the entrywise topology, which equals the operator-norm topology. The partial transpose exchanges the $i$-th indices only, with no complex conjugation. Product post-processing may be randomized; this gives the convex hull of the deterministic events, and all profiles are unchanged.
-- source:
--   Ji Guan, Yecheng Qin, Parallel Composition of Quantum Differential Privacy: The Role of Measurement Restrictions, STOC 2027 submission #1640 (October 2026), source.pdf SHA-256 da23c8347251683a16df4c61de3fa1604211cdbf34d757a7a45feb0efd54c694, §2.2 Measurement Classes (printed p. 13 / PDF p. 14)

import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_WildeQIT_EntBreaking_IsQuantumChannel

/-!
# Measurement classes on `n` output sites: Product, LOCC, SEP, PPT(i), PPT, ALL

Ji Guan, Yecheng Qin, *Parallel Composition of Quantum Differential Privacy: The Role of
Measurement Restrictions*, STOC 2027 submission #1640 (October 2026), §2.2 (printed p. 13 /
PDF p. 14).

The output has one site per register, `K = ⨂_{j=1}^n K_j`; here every site is `ℂ^d`, so an
operator on `K` is a matrix indexed by `Fin n → Fin d` (`d = 2` for qubit channels). An event of a
POVM `{M_z}_{z ∈ Ω}` is an effect `∑_{z ∈ S} M_z`, `S ⊆ Ω`, and `E(M)` is the set of events of the
POVMs of class `M`; each set below contains `0` and `I` and is closed under `M ↦ I − M`.
-/

namespace GuanQinQDP.Restricted

open QAlgorithms
open scoped Matrix ComplexOrder

/-- The product operator `P_1 ⊗ ⋯ ⊗ P_n` on `n` sites of dimension `d`. -/
def piKron {n d : ℕ} (P : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  Matrix.of fun x y => ∏ j, P j (x j) (y j)

/-- §2.2: the partial transpose `M^{T_i}` on site `i` in the computational basis (basis
transpose of the `i`-th index only, no complex conjugation):
`(M^{T_i})_{x, y} = M_{(y_i, x_{-i}), (x_i, y_{-i})}`. -/
def partialTransposeAt {n d : ℕ} (i : Fin n) (M : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  Matrix.of fun x y => M (Function.update x i (y i)) (Function.update y i (x i))

/-- §2.2: `E^{(i)}_PPT = {M : 0 ⪯ M ⪯ I, 0 ⪯ M^{T_i} ⪯ I}`, the events PPT across the single cut
between site `i` and the other sites (class PPT(i)). -/
def pptEventsAt {n d : ℕ} (i : Fin n) : Set (Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :=
  {M | IsEffect M ∧ IsEffect (partialTransposeAt i M)}

/-- §2.2: `E_PPT = ⋂_{i=1}^n E^{(i)}_PPT`: PPT across every **single-site** cut (not across every
bipartition). -/
def pptEvents (n d : ℕ) : Set (Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :=
  {M | IsEffect M ∧ ∀ i : Fin n, IsEffect (partialTransposeAt i M)}

/-- A fully separable positive operator on `n` sites: a finite sum of products
`P_{k,1} ⊗ ⋯ ⊗ P_{k,n}` of positive semidefinite factors (no trace normalization; `0` is the
empty sum). -/
def IsFullySeparable {n d : ℕ} (X : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) : Prop :=
  ∃ q : ℕ, ∃ P : Fin q → Fin n → Matrix (Fin d) (Fin d) ℂ,
    (∀ k j, (P k j).PosSemidef) ∧ X = ∑ k, piKron (P k)

/-- §2.2, SEP: the events of separable POVMs, i.e. the effects `M` such that both `M` and
`I − M` are fully separable across the `n` output sites. (Every event of a separable POVM has
this form, and such an `M` is an event of the separable POVM `{M, I − M}`.) -/
def sepEvents (n d : ℕ) : Set (Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :=
  {M | IsEffect M ∧ IsFullySeparable M ∧ IsFullySeparable (1 - M)}

/-- §2.2, Product: local POVMs with classical post-processing. Every site `j` measures a POVM
`{P_{j,z}}_{z ∈ Fin m}` (finitely many outcomes; padding with zero elements makes the outcome sets
of the sites equal), and the outcome tuple `z` is accepted with probability `f(z) ∈ [0, 1]`
(randomized classical post-processing; `f` a `{0,1}`-valued indicator gives the plain events
`∑_{z ∈ S}`). The event is `∑_z f(z) P_{1,z_1} ⊗ ⋯ ⊗ P_{n,z_n}`. -/
def productEvents (n d : ℕ) : Set (Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :=
  {M | ∃ m : ℕ, ∃ P : Fin n → Fin m → Matrix (Fin d) (Fin d) ℂ,
    (∀ j z, (P j z).PosSemidef) ∧ (∀ j, ∑ z, P j z = 1) ∧
    ∃ f : (Fin n → Fin m) → ℝ, (∀ z, 0 ≤ f z ∧ f z ≤ 1) ∧
      M = ∑ z : Fin n → Fin m, (f z : ℂ) • piKron fun j => P j (z j)}

/-- The local operator `I ⊗ ⋯ ⊗ K ⊗ ⋯ ⊗ I` with `K : ℂ^{d_j} → ℂ^{d'}` at site `j`: site `j`
changes dimension from `d_j` to `d'` (local ancillas or discarding), the other sites are
untouched. -/
def liftLocal {n : ℕ} {d : Fin n → ℕ} (j : Fin n) {d' : ℕ} (K : Matrix (Fin d') (Fin (d j)) ℂ) :
    Matrix ((k : Fin n) → Fin (Function.update d j d' k)) ((k : Fin n) → Fin (d k)) ℂ :=
  open Classical in
  Matrix.of fun y x =>
    if ∀ k, k ≠ j → ((y k : ℕ) = (x k : ℕ)) then
      K (Fin.cast (Function.update_self j d' d) (y j)) (x j)
    else 0

/-- §2.2, LOCC, finite rounds: the events of `n`-party protocols of local operations and
classical communication, the local system of party `k` having dimension `d k` (local memories of
any finite dimension; no shared entanglement, no quantum communication). Inductively:

* `reject`, `accept`: with no further operation the protocol stops and outputs reject (event `0`)
  or accept (event `I`);
* `round`: party `j` applies a local quantum instrument with Kraus operators
  `K_a : ℂ^{d_j} → ℂ^{d'}`, `∑_a K_a† K_a = I` (finitely many outcomes, arbitrary new local
  dimension `d'`), broadcasts the outcome `a`, and the parties continue with a protocol whose
  accepting event `E_a` may depend on `a`. The event is `∑_a (I ⊗ K_a)† E_a (I ⊗ K_a)`.

Local unitaries, ancillas, local randomness, discarding and final local measurements with
arbitrary classical grouping are special cases. The number of rounds of each protocol is finite
but unbounded. -/
inductive IsLOCCEventFin {n : ℕ} :
    (d : Fin n → ℕ) → Matrix ((k : Fin n) → Fin (d k)) ((k : Fin n) → Fin (d k)) ℂ → Prop
  | reject (d : Fin n → ℕ) : IsLOCCEventFin d 0
  | accept (d : Fin n → ℕ) : IsLOCCEventFin d 1
  | round (d : Fin n → ℕ) (j : Fin n) (d' m : ℕ) (K : Fin m → Matrix (Fin d') (Fin (d j)) ℂ)
      (hK : ∑ a, (K a)ᴴ * K a = 1)
      (E : Fin m → Matrix ((k : Fin n) → Fin (Function.update d j d' k))
        ((k : Fin n) → Fin (Function.update d j d' k)) ℂ)
      (hE : ∀ a, IsLOCCEventFin (Function.update d j d') (E a)) :
      IsLOCCEventFin d (∑ a, (liftLocal j (K a))ᴴ * E a * liftLocal j (K a))

/-- §2.2, LOCC: the closure (entrywise topology, i.e. operator-norm topology) of the events of
finite-round LOCC protocols on `n` sites of dimension `d`. The closure adds the limits of
finite-round events (for instance unbounded-round protocols); all of them remain PPT events,
since the PPT event set is closed. -/
def loccEvents (n d : ℕ) : Set (Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :=
  closure {M | IsLOCCEventFin (fun _ => d) M}

/-- §2.2, ALL: every effect. -/
def allEvents (n d : ℕ) : Set (Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :=
  {M | IsEffect M}

/-- The measurement classes of §2.2 (PPT(i) is `pptEventsAt i`). -/
inductive MeasClass
  | product
  | locc
  | sep
  | ppt
  | all
  deriving DecidableEq

/-- The event set `E(M)` of a measurement class on `n` output sites of dimension `d`. -/
def eventSet (n d : ℕ) : MeasClass → Set (Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ)
  | .product => productEvents n d
  | .locc => loccEvents n d
  | .sep => sepEvents n d
  | .ppt => pptEvents n d
  | .all => allEvents n d

/-! ### Sanity checks -/

/-- The partial transpose is an involution. -/
example {n d : ℕ} (i : Fin n) (M : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :
    partialTransposeAt i (partialTransposeAt i M) = M := by
  ext x y
  simp [partialTransposeAt]

/-- On two qubits, `T_0` swaps the first indices: `(M^{T_0})_{(x₀,x₁),(y₀,y₁)} = M_{(y₀,x₁),(x₀,y₁)}`. -/
example (M : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ) (x y : Fin 2 → Fin 2) :
    partialTransposeAt 0 M x y = M ![y 0, x 1] ![x 0, y 1] := by
  simp only [partialTransposeAt, Matrix.of_apply]
  congr 1 <;> ext k <;> fin_cases k <;> simp

/-- `0` and `I` are finite-round LOCC events, hence LOCC events. -/
example (n d : ℕ) : (0 : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) ∈ loccEvents n d ∧
    (1 : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) ∈ loccEvents n d :=
  ⟨subset_closure (IsLOCCEventFin.reject _), subset_closure (IsLOCCEventFin.accept _)⟩

/-- `I` is fully separable (one product term `I ⊗ ⋯ ⊗ I`). -/
example (n d : ℕ) : IsFullySeparable (1 : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) := by
  refine ⟨1, fun _ _ => 1, fun _ _ => Matrix.PosSemidef.one, ?_⟩
  ext x y
  simp only [Finset.univ_unique, Finset.sum_singleton, piKron, Matrix.of_apply, Matrix.one_apply]
  by_cases h : x = y
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
      by_contra hc; push Not at hc; exact h (funext hc)
    exact (Finset.prod_eq_zero (f := fun k => if x k = y k then (1 : ℂ) else 0)
      (Finset.mem_univ j) (if_neg hj)).symm

end GuanQinQDP.Restricted


