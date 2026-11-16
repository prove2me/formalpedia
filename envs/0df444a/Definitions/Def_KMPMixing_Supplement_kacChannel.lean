-- Prove2me | Definitions.Def_KMPMixing_Supplement_kacChannel
-- name    : KMPMixing_Supplement_kacChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:55:06.7022+00:00
-- url     : https://prove2.me/theorems/8bd2777f-772c-4919-bb27-f8594a127969
-- title:
--   The parallel Kac twirl $\Phi^t_{\mathrm{Kac}}$, the Haar twirl $\Phi^t_{\mathrm{Haar}}$ and $\Pi_{\mathrm{Sym}}$
-- statement:
--   Let $d$ be even. Operators on $(\mathbb C^d)^{\otimes t}$ are written in the computational basis $|x\rangle$, $x\in[d]^t$, and $U^{\otimes t}$ has entries $(U^{\otimes t})_{y,x}=\prod_\ell U_{y_\ell,x_\ell}$.
--
--   1. One step of the **parallel Kac walk** is the random unitary $K=P_\tau W$: $W=\sum_{i=1}^{d/2}|i\rangle\langle i|\otimes W_i$ is block diagonal, the blocks $W_i$ are independent Haar-random unitaries in $\mathrm U(2)$ acting on the basis vectors $\{2i-1,2i\}$, and $P_\tau=\sum_x|\tau(x)\rangle\langle x|$ for a uniformly random $\tau\in S_d$ independent of $W$.
--   2. With a reference system $\mathbb C^m$,
--   $$
--   (\Phi^t_{\mathrm{Kac}}\otimes1)(X)=\mathbb E_K\big[(K^{\otimes t}\otimes I)\,X\,(K^{\otimes t}\otimes I)^\dagger\big],\qquad
--   (\Phi^t_{\mathrm{Haar}}\otimes1)(X)=\mathbb E_{U\sim\nu_{\mathrm{Haar}}}\big[(U^{\otimes t}\otimes I)\,X\,(U^{\otimes t}\otimes I)^\dagger\big],
--   $$
--   where $\nu_{\mathrm{Haar}}$ is the Haar probability measure on $\mathrm U(d)$.
--   3. $\Pi_{\mathrm{Sym}}$ is the projector onto the symmetric subspace $\vee^t\mathbb C^d=\mathrm{span}\{|u\rangle^{\otimes t}\}$, written as $\frac1{t!}\sum_{\pi\in S_t}P_\pi$ over the operators permuting the tensor factors.
--
--   Theorem 6.1 bounds the distance between $\Phi^{t,k+1}_{\mathrm{Kac}}\otimes1$ (the $(k+1)$-fold composition) and $\Phi^t_{\mathrm{Haar}}\otimes1$ on states supported on $\vee^t\mathbb C^d$.
--
--   **Formalization Note** Operators on $(\mathbb C^d)^{\otimes t}\otimes\mathbb C^m$ are matrices indexed by `(Fin t → Fin d) × Fin m`, and $A\otimes I$ is the Kronecker product. With the 0-indexed basis `Fin d`, block $b$ acts on $\{2b,2b+1\}$. The Haar measures are the normalized Haar measures on `Matrix.unitaryGroup` (topology induced from the entries, Borel σ-algebra); the expectation over $W$ is an entrywise integral against the product of $d/2$ copies of the Haar measure on $\mathrm U(2)$, and the one over $\tau$ is a uniform average over $S_d$. By linearity the map defined with $\otimes I$ inside the expectation is $\Phi\otimes1$, and its iterates are $\Phi^{t,k}\otimes1$.
-- source:
--   Chen, Liu, Qin, Schulman, Song, Yao, Zhao, A Tale of Two Walks: From Kac to KMP and Back, arXiv:2609.38044 (sha256 6a9abdd4…), Eqs. (31)–(34), pp.39–40 (PDF pp.41–42); symmetric subspace and Eq. (4), p.13 (PDF p.15)

import Mathlib

namespace KMPMixing.Supplement

open MeasureTheory
open scoped ComplexOrder Kronecker Matrix

/-- The unitary group `U(d)` of `d × d` complex matrices, with the topology induced from the
entrywise topology on matrices and its Borel σ-algebra. -/
abbrev UGroup (d : ℕ) := Matrix.unitaryGroup (Fin d) ℂ

instance unitaryGroup_compactSpace (d : ℕ) : CompactSpace (UGroup d) := by
  have hclosed : IsClosed (Matrix.unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) :=
    isClosed_unitary
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : ℂ) 1).matrix.of_isClosed_subset hclosed
  intro a ha i j
  have : NeZero d := ⟨fun h => by subst h; exact Fin.elim0 i⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  let a' : CStarMatrix (Fin d) (Fin d) ℂ := CStarMatrix.ofMatrix a
  have hu : a' ∈ unitary (CStarMatrix (Fin d) (Fin d) ℂ) := ha
  exact CStarMatrix.norm_entry_le_norm.trans (le_of_eq (CStarRing.norm_of_mem_unitary hu))

instance unitaryGroup_secondCountable (d : ℕ) : SecondCountableTopology (UGroup d) :=
  haveI : SecondCountableTopology (Matrix (Fin d) (Fin d) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℂ))
  (Topology.IsInducing.subtypeVal :
    Topology.IsInducing (Subtype.val : UGroup d → Matrix (Fin d) (Fin d) ℂ)).secondCountableTopology

noncomputable instance unitaryGroup_measurableSpace (d : ℕ) : MeasurableSpace (UGroup d) :=
  borel (UGroup d)

instance unitaryGroup_borelSpace (d : ℕ) : BorelSpace (UGroup d) := ⟨rfl⟩

/-- The normalization set of the Haar measure on `U(d)`: the whole (compact) group. -/
def univCompacts (d : ℕ) : TopologicalSpace.PositiveCompacts (UGroup d) :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

/-- `ν_Haar`, the **Haar probability measure** on `U(d)` (arXiv:2609.38044, Eq. (34), p.40
(PDF p.42), and the blocks `W_i` of Eq. (31), p.39 (PDF p.41)): the left-invariant Haar measure
normalized to total mass `1`. -/
noncomputable def haarU (d : ℕ) : Measure (UGroup d) := Measure.haarMeasure (univCompacts d)

instance haarU_isProbabilityMeasure (d : ℕ) : IsProbabilityMeasure (haarU d) :=
  ⟨by simpa [haarU, univCompacts] using Measure.haarMeasure_self (K₀ := univCompacts d)⟩

/-- `U^{⊗t}` acting on `(ℂ^d)^{⊗t}` in the computational basis indexed by strings
`x : Fin t → Fin d`: `(U^{⊗t})_{y,x} = ∏_ℓ U_{y_ℓ, x_ℓ}`. -/
def tensorPow {d : ℕ} (t : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin t → Fin d) (Fin t → Fin d) ℂ :=
  Matrix.of fun y x => ∏ ℓ, A (y ℓ) (x ℓ)

/-- `Π_Sym`, the projector onto the **symmetric subspace** `∨^t ℂ^d = span{|u⟩^{⊗t}}` of
`(ℂ^d)^{⊗t}` (arXiv:2609.38044, §2 "Symmetric subspace", p.13 (PDF p.15)).

**Formalization Note** It is written as the average `(1/t!) Σ_{π ∈ S_t} P_π` of the operators
permuting the `t` tensor factors (`P_π |x⟩ = |x ∘ π⁻¹⟩`), which is the orthogonal projector onto
`∨^t ℂ^d`; it equals `Σ_r |D_r⟩⟨D_r|` over the generalized Dicke states of Eq. (4). -/
noncomputable def symProj (d t : ℕ) : Matrix (Fin t → Fin d) (Fin t → Fin d) ℂ :=
  ((t.factorial : ℂ))⁻¹ • ∑ π : Equiv.Perm (Fin t),
    Matrix.of fun y x : Fin t → Fin d => if y = x ∘ π then (1 : ℂ) else 0

/-- The permutation unitary `P_τ = Σ_x |τ(x)⟩⟨x|` on `ℂ^d` (arXiv:2609.38044, Eq. (31), p.39
(PDF p.41)). -/
def permMatrix {d : ℕ} (τ : Equiv.Perm (Fin d)) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun y x => if y = τ x then 1 else 0

/-- The block-diagonal unitary `W = Σ_{i=1}^{d/2} |i⟩⟨i| ⊗ W_i` of Eq. (31) (arXiv:2609.38044,
p.39 (PDF p.41)): block `i` acts as the `2 × 2` unitary `W_i` on the basis vectors
`{2i − 1, 2i}`.

**Formalization Note** With 0-indexed basis `Fin d`, block `b : Fin (d/2)` acts on the basis
vectors `{2b, 2b + 1}`: the entry `(y, x)` is `(W_{⌊x/2⌋})_{y mod 2, x mod 2}` when `y` and `x`
lie in the same block and `0` otherwise. For even `d` every basis vector lies in a block. -/
def blockDiag {d : ℕ} (W : Fin (d / 2) → UGroup 2) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun y x =>
    if h : y.val / 2 = x.val / 2 ∧ x.val / 2 < d / 2 then
      (W ⟨x.val / 2, h.2⟩).1 ⟨y.val % 2, Nat.mod_lt _ two_pos⟩ ⟨x.val % 2, Nat.mod_lt _ two_pos⟩
    else 0

/-- The law of the blocks `(W_1, …, W_{d/2})`: independent Haar-random unitaries in `U(2)`
(arXiv:2609.38044, Eq. (31), p.39 (PDF p.41)). -/
noncomputable def blockLaw (b : ℕ) : Measure (Fin b → UGroup 2) := Measure.pi fun _ => haarU 2

instance blockLaw_isProbabilityMeasure (b : ℕ) : IsProbabilityMeasure (blockLaw b) := by
  unfold blockLaw; infer_instance

/-- The entrywise expectation `E_a[F(a)]` of a random complex matrix. -/
noncomputable def matrixIntegral {ι κ α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : α → Matrix ι κ ℂ) : Matrix ι κ ℂ :=
  Matrix.of fun i j => ∫ a, F a i j ∂μ

/-- The one-step **parallel Kac twirl** with a reference system,
`(Φ^t_Kac ⊗ 1)(X) = E_K[(K^{⊗t} ⊗ I) X (K^{⊗t} ⊗ I)†]` with `K = P_τ W`
(arXiv:2609.38044, Eqs. (31)–(32), p.39 (PDF p.41)): `W` is block diagonal with independent
Haar-random `U(2)` blocks and `τ` is a uniformly random permutation in `S_d`, independent of `W`.

**Formalization Note** Operators on `(ℂ^d)^{⊗t} ⊗ ℂ^m` are matrices indexed by
`(Fin t → Fin d) × Fin m`, and `A ⊗ I` is the Kronecker product `A ⊗ₖ 1`. The `τ`-average is the
uniform average over `Equiv.Perm (Fin d)`, the `W`-average the entrywise integral against
`blockLaw (d / 2)`. By linearity this is `Φ^t_Kac ⊗ 1` applied to `X`. -/
noncomputable def kacChannel (d t m : ℕ) (X : Matrix ((Fin t → Fin d) × Fin m)
    ((Fin t → Fin d) × Fin m) ℂ) : Matrix ((Fin t → Fin d) × Fin m) ((Fin t → Fin d) × Fin m) ℂ :=
  ((Fintype.card (Equiv.Perm (Fin d)) : ℂ))⁻¹ • ∑ τ : Equiv.Perm (Fin d),
    matrixIntegral (blockLaw (d / 2)) fun W =>
      (tensorPow t (permMatrix τ * blockDiag W) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * X *
        (tensorPow t (permMatrix τ * blockDiag W) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))ᴴ

/-- The **Haar twirl** with a reference system,
`(Φ^t_Haar ⊗ 1)(X) = E_{U ∼ ν_Haar}[(U^{⊗t} ⊗ I) X (U^{⊗t} ⊗ I)†]` (arXiv:2609.38044, Eq. (34),
p.40 (PDF p.42)).

**Formalization Note** Same conventions as `kacChannel`; `ν_Haar` is `haarU d`. -/
noncomputable def haarChannel (d t m : ℕ) (X : Matrix ((Fin t → Fin d) × Fin m)
    ((Fin t → Fin d) × Fin m) ℂ) : Matrix ((Fin t → Fin d) × Fin m) ((Fin t → Fin d) × Fin m) ℂ :=
  matrixIntegral (haarU d) fun U =>
    (tensorPow t U.1 ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * X *
      (tensorPow t U.1 ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))ᴴ

end KMPMixing.Supplement


