-- Prove2me | Definitions.Def_QuantumStateIdentity321_Schur_Supplement_SchurSampling
-- name    : QuantumStateIdentity321_Schur_Supplement_SchurSampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:51:45.765026+00:00
-- url     : https://prove2.me/theorems/e8bc067e-9a18-49be-9e77-a7e51b77da10
-- title:
--   Jucys–Murphy operators, Young's orthogonal form, the Schur transform, the measurement $\{M_{\lambda,S}\}$ and Algorithm 3 with exact Schur transforms
-- statement:
--   This module defines the objects of §2.2 and §4.
--
--   1. $S_n$ acts on $(\mathbb C^d)^{\otimes n}$ by $P(\pi)|i_1,\dots,i_n\rangle=|i_{\pi^{-1}(1)},\dots,i_{\pi^{-1}(n)}\rangle$, and $P(J_i)=\sum_{j<i}P((j\,i))$ is the represented Jucys–Murphy element, a sum of SWAP operators ($P(J_1)=0$).
--   2. For a Young diagram $\lambda$ with $n$ boxes, $\kappa_\lambda$ is the representation of $S_n$ on $\mathbb C^{\mathrm{SYT}(\lambda)}$ in **Young's orthogonal form**: for an adjacent transposition $(k,k+1)$ and a standard tableau $T$ with $r=\mathrm{ct}_T(k+1)-\mathrm{ct}_T(k)$, $\kappa_\lambda((k,k+1))|T\rangle=r^{-1}|T\rangle+\sqrt{1-r^{-2}}\,|(k,k+1)T\rangle$ (the second term only when $(k,k+1)T$ is standard). The content of a box is column minus row, and $\mathrm{ct}_S(i)$ is the content of the box of $S$ containing $i$.
--   3. A **Schur transform** is a unitary $U$ from $(\mathbb C^d)^{\otimes n}$ onto $\bigoplus_\lambda\mathrm{Sp}_\lambda\otimes\mathbb C^{m_\lambda}$ with $UP(\pi)U^\dagger=\bigoplus_\lambda\kappa_\lambda(\pi)\otimes I$ for every $\pi$.
--   4. (22): $M_{\lambda,S}=U^\dagger(|\lambda\rangle\langle\lambda|\otimes|S\rangle\langle S|\otimes I)U$, for $S$ a standard tableau of shape $\lambda$ with $\ell(\lambda)\le d$ rows.
--   5. **Algorithm 3** with exact Schur transforms, $R$ rounds and threshold $\tau$: in round $r$ the measurement $\{M_{\lambda,S}\}$ is performed on the forward block $|\psi_1\rangle\otimes\cdots\otimes|\psi_n\rangle$ (copy $2r$ of each state) and on the reverse block $|\psi_n\rangle\otimes\cdots\otimes|\psi_1\rangle$ (copy $2r+1$), with outcomes $S_r,S'_r$; $Z_{i,r}=\mathrm{ct}_{S_r}(i)+\mathrm{ct}_{S'_r}(n+1-i)$, $\bar Z_i=\frac1R\sum_rZ_{i,r}$, and the protocol rejects iff $\min_i\bar Z_i<\tau$. Its accept effect on $2R$ copies of each state is the sum over accepted outcome records of the tensor product of the $2R$ measured projectors. The parameters are $\tau=\frac{3n-4}4-\frac{n-2}2\varepsilon+\frac{n-2}4\sqrt\varepsilon$, $L=\lceil(8/\gamma^2)\log(2n/\delta)\rceil$ and the soundness-only $\lceil(8/\gamma^2)\log(2/\delta)\rceil$.
--
--   These are the objects of Lemma 2.3, Corollary 4.1, Lemma 4.2 and Theorems 4.3–4.4.
--
--   **Formalization Note** Tableaux, shapes, contents and the Young-orthogonal matrices are those of the published module `QAlgorithms_Papers_Independent_Intakenext100_P78` (a tableau is the injective list of its boxes whose prefixes are lower sets; label $i$ is the source's $i+1$, and $n+1-i$ is `Fin.rev i`). $\kappa_\lambda$ is the representation with those matrices on the adjacent transpositions (its existence is part of Lemma 2.3); $M_{\lambda,S}$ uses a chosen Schur transform, and does not depend on the choice. The transform is required to intertwine only the $S_n$ action, which is all (22) uses; the $GL(d)$ action of (8) only refines it. The defaults of the choices (trivial representation, zero projector) arise only if the objects did not exist, which Lemma 2.3 and Corollary 4.1 exclude.
-- source:
--   Shih-Han Hung, Ming-Hsien Tsai, STOC 2027 submission #321 (October 2026), §2.2 (6), (8)–(10), §4 Algorithm 3 and (22), PDF/printed p.7–8, 14, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/321.pdf

import Definitions.Def_QuantumStateIdentity321_Schur_Model
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P78

/-!
# Jucys–Murphy operators, Young's orthogonal form, the Schur transform, Schur sampling with the
# tableau retained, and Algorithm 3 with exact Schur transforms

Shih-Han Hung, Ming-Hsien Tsai, *Efficient Quantum State Identity Testing*, STOC 2027
submission #321 (October 2026), §2.1–§2.2 (pp.6–8), §4 (pp.13–17, Algorithm 3 and (22)).

Standard Young tableaux, their shapes, box contents and the Young-orthogonal matrices of the
adjacent transpositions are the published definitions of
`QAlgorithms.Papers.Independent.Intakenext100.P78` (a tableau with `n` boxes is the injective
list of its boxes `t i = (row, column)`, zero-based, whose every prefix is a lower set; label
`i : Fin n` is the source's `i + 1`; the content of a box is column − row).
-/

namespace QuantumStateIdentity321.Schur.Supplement

open Matrix
open QAlgorithms.Papers.Independent.Intakenext100.P78

attribute [local instance] Classical.propDecidable

/-- A standard Young tableau with `n` boxes (of any shape). -/
abbrev SYT (n : ℕ) := BoundedYoungPath n

/-- The shape (Young diagram) of a standard Young tableau, as its set of boxes. -/
noncomputable def shape {n : ℕ} (S : SYT n) : Finset (Fin n × Fin n) := youngPathEndpoint S

/-- Definition 2.1, p.7: `ct_S(i)`, the content (column − row) of the box of `S` containing the
label `i`. -/
def content {n : ℕ} (S : SYT n) (i : Fin n) : ℤ := boundedBoxContent (S.val i)

/-- The length `ℓ(λ)` of a Young diagram: its number of nonzero rows, i.e. the number of boxes
in its first column. -/
noncomputable def numRows {n : ℕ} (μ : Finset (Fin n × Fin n)) : ℕ :=
  (μ.filter (fun b => b.2.val = 0)).card

/-! ## The permutation action and the Jucys–Murphy operators -/

/-- (6), p.7: the natural action `P(π)|i₁, …, iₙ⟩ = |i_{π⁻¹(1)}, …, i_{π⁻¹(n)}⟩` of `S_n` on
`(ℂᵈ)^{⊗n}`, in the basis `Fin n → Fin d`: `P(π)` maps the basis word `w` to `w ∘ π⁻¹`. -/
def permOp {n d : ℕ} (π : Equiv.Perm (Fin n)) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  fun v w => if v = w ∘ ⇑π⁻¹ then 1 else 0

/-- (9)–(10), p.8: the represented Jucys–Murphy operator `P(J_i) = Σ_{j<i} P((j i))`, the sum
of the SWAP operators of the tensor factors `j < i` with factor `i` (`P(J₁) = 0`). -/
noncomputable def jmOp {n d : ℕ} (i : Fin n) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i), permOp (Equiv.swap j i)

/-! ## Young's orthogonal form -/

/-- A representation `ρ` of `S_n` on `ℂ^{SYT(λ)}` is *in Young's orthogonal form* if every
adjacent transposition `(k, k+1)` acts by the published Young-orthogonal matrix: for a tableau
`T` with `r = ct_T(k+1) − ct_T(k)`, `ρ((k,k+1))|T⟩ = r⁻¹|T⟩ + √(1 − r⁻²)|(k,k+1)T⟩` (the second
term only when `(k,k+1)T` is standard). Since the adjacent transpositions generate `S_n`, at most
one such representation exists. -/
def IsYoungOrthogonalRep {n : ℕ} (μ : Finset (Fin n × Fin n))
    (ρ : Equiv.Perm (Fin n) →* Matrix (YoungEndpointPaths n μ) (YoungEndpointPaths n μ) ℂ) :
    Prop :=
  ∀ k : Fin n, k.val + 1 < n → ρ (Equiv.swap k (nextIndex k)) = youngAdjacent μ k

/-- §2.2, p.7: `κ_λ`, the irreducible representation of `S_n` on the Specht module `Sp_λ` written
in Young's orthogonal basis `{|S⟩ : S ∈ SYT(λ)}`: the representation determined by Young's
orthogonal form on the adjacent transpositions. (That such a representation exists is a theorem,
stated in Lemma 2.3; this definition takes it when it exists.) -/
noncomputable def kappa {n : ℕ} (μ : Finset (Fin n × Fin n)) :
    Equiv.Perm (Fin n) →* Matrix (YoungEndpointPaths n μ) (YoungEndpointPaths n μ) ℂ :=
  if h : ∃ ρ, IsYoungOrthogonalRep μ ρ then Classical.choose h else 1

/-- `κ_λ(J_i) = Σ_{j<i} κ_λ((j i))`, the Jucys–Murphy element in the Specht representation. -/
noncomputable def kappaJM {n : ℕ} (μ : Finset (Fin n × Fin n)) (i : Fin n) :
    Matrix (YoungEndpointPaths n μ) (YoungEndpointPaths n μ) ℂ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i), kappa μ (Equiv.swap j i)

/-! ## The Schur transform and the measurement `{M_{λ,S}}` -/

/-- Labels of a Schur basis with multiplicity spaces of dimension `mult λ`: a pair `(S, t)` of a
standard Young tableau `S` (whose shape is `λ`) and a multiplicity index `t < mult λ`. -/
abbrev SchurLabel (n : ℕ) (mult : Finset (Fin n × Fin n) → ℕ) :=
  Σ S : SYT n, Fin (mult (shape S))

/-- The block-diagonal action `⊕_λ |λ⟩⟨λ| ⊗ κ_λ(π) ⊗ I_{mult λ}` in the labels `(S, t)`. -/
noncomputable def schurBlock {n : ℕ} (mult : Finset (Fin n × Fin n) → ℕ)
    (π : Equiv.Perm (Fin n)) : Matrix (SchurLabel n mult) (SchurLabel n mult) ℂ :=
  fun a b =>
    if h : shape a.1 = shape b.1 then
      (if a.2.val = b.2.val then kappa (shape a.1) π ⟨a.1, rfl⟩ ⟨b.1, h.symm⟩ else 0)
    else 0

/-- (8), p.7, symmetric-group part: a Schur transform is a unitary `U` from `(ℂᵈ)^{⊗n}` to
`⊕_λ Sp_λ ⊗ ℂ^{mult λ}` with `U P(π) U† = ⊕_λ κ_λ(π) ⊗ I` for every `π ∈ S_n`, with `κ_λ` in
Young's orthogonal basis. (By Schur–Weyl duality `mult λ = dim V_λ^d`, which is `0` exactly when
`ℓ(λ) > d`, and the multiplicity register carries the action `ν_λ^d` of `GL(d)`.) -/
structure SchurTransform (n d : ℕ) where
  /-- The dimension of the multiplicity register of each shape. -/
  mult : Finset (Fin n × Fin n) → ℕ
  /-- The transform, from the computational basis to the Schur labels. -/
  U : Matrix (SchurLabel n mult) (Fin n → Fin d) ℂ
  /-- `U†U = I`. -/
  isometry : Matrix.conjTranspose U * U = 1
  /-- `UU† = I`. -/
  coisometry : U * Matrix.conjTranspose U = 1
  /-- `U P(π) U† = ⊕_λ κ_λ(π) ⊗ I` for every permutation. -/
  intertwines : ∀ π : Equiv.Perm (Fin n),
    U * permOp (d := d) π * Matrix.conjTranspose U = schurBlock mult π

/-- (22), p.14: `M_{λ,S} = U†(|λ⟩⟨λ| ⊗ |S⟩⟨S| ⊗ I)U`, the projector of the measurement of the
Young-diagram label `λ` and the tableau label `S` of the symmetric-group register after the Schur
transform, leaving the unitary register unmeasured (`λ` is the shape of `S`). It does not depend
on the choice of the Schur transform; one is chosen when it exists. -/
noncomputable def schurProj {n d : ℕ} (S : SYT n) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  if h : Nonempty (SchurTransform n d) then
    Matrix.conjTranspose (Classical.choice h).U *
      Matrix.diagonal (fun a : SchurLabel n (Classical.choice h).mult =>
        if a.1 = S then (1 : ℂ) else 0) * (Classical.choice h).U
  else 0

/-- The outcomes `(λ, S)` of the measurement `{M_{λ,S}}` on `(ℂᵈ)^{⊗n}` (22)–(24): standard Young
tableaux `S` with `n` boxes whose shape `λ` has `ℓ(λ) ≤ d` rows (`λ` is recorded as the shape of
`S`). -/
abbrev SchurOutcome (n d : ℕ) := {S : SYT n // numRows (shape S) ≤ d}

/-- The Born probability `⟨Ψ|M|Ψ⟩` of an outcome with projector `M` on the (unnormalized) vector
`Ψ`. -/
noncomputable def bornProb {X : Type} [Fintype X] (M : Matrix X X ℂ) (Ψ : X → ℂ) : ℝ :=
  (star Ψ ⬝ᵥ (M *ᵥ Ψ)).re

/-- The forward-ordered block `|ψ₁⟩ ⊗ ⋯ ⊗ |ψₙ⟩` (amplitude `∏_p ψ_p(w p)`). -/
noncomputable def forwardInput {n d : ℕ} (ψ : Fin n → State d) : (Fin n → Fin d) → ℂ :=
  fun w => ∏ p : Fin n, ψ p (w p)

/-- The reverse-ordered block `|ψₙ⟩ ⊗ ⋯ ⊗ |ψ₁⟩`: tensor factor `p` holds `|ψ_{n+1−p}⟩`
(`Fin.rev p` in zero-based labels). -/
noncomputable def reverseInput {n d : ℕ} (ψ : Fin n → State d) : (Fin n → Fin d) → ℂ :=
  fun w => ∏ p : Fin n, ψ (Fin.rev p) (w p)

/-! ## Algorithm 3 with exact Schur transforms (p.14) -/

/-- Step 1 of Algorithm 3: `τ = (3n−4)/4 − ((n−2)/2)ε + ((n−2)/4)√ε`. -/
noncomputable def alg3Threshold (n : ℕ) (ε : ℝ) : ℝ :=
  (3 * (n : ℝ) - 4) / 4 - ((n : ℝ) - 2) / 2 * ε + ((n : ℝ) - 2) / 4 * Real.sqrt ε

/-- Step 2 of Algorithm 3: `L = ⌈(8/γ²) log(2n/δ)⌉` rounds, `γ = 1/2 − √ε`. -/
noncomputable def alg3Rounds (n : ℕ) (ε δ : ℝ) : ℕ :=
  ⌈8 / (1 / 2 - Real.sqrt ε) ^ 2 * Real.log (2 * n / δ)⌉₊

/-- Theorem 4.3's soundness-only round count `⌈(8/γ²) log(2/δ)⌉`. -/
noncomputable def alg3RoundsSound (ε δ : ℝ) : ℕ :=
  ⌈8 / (1 / 2 - Real.sqrt ε) ^ 2 * Real.log (2 / δ)⌉₊

/-- Steps 3–5 of Algorithm 3 on recorded outcomes `o r = ((λ_r, S_r), (λ'_r, S'_r))` of the
`R` rounds:
`Z_{i,r} = ct_{S_r}(i) + ct_{S'_r}(n+1−i)`, `Z̄_i = (1/R) Σ_r Z_{i,r}`; the protocol rejects iff
`min_i Z̄_i < τ`, so it accepts iff `Z̄_i ≥ τ` for every `i`. -/
def alg3Accepts {n d : ℕ} (R : ℕ) (τ : ℝ) (o : Fin R → SchurOutcome n d × SchurOutcome n d) :
    Prop :=
  ∀ i : Fin n, τ ≤ (1 / (R : ℝ)) *
    ∑ r : Fin R, ((content (o r).1.val i : ℝ) + (content (o r).2.val (Fin.rev i) : ℝ))

/-- In round `r` the forward block is copy `2r` of every state, in the order `ψ₁, …, ψₙ`. -/
def forwardBlock {n d R : ℕ} (r : Fin R) (w : CopyBasis n (2 * R) d) : Fin n → Fin d :=
  fun p => w (p, ⟨2 * r.val, by omega⟩)

/-- In round `r` the reverse block is copy `2r+1` of every state, in the order `ψₙ, …, ψ₁`:
its tensor factor `p` is the register of state `n+1−p`. -/
def reverseBlock {n d R : ℕ} (r : Fin R) (w : CopyBasis n (2 * R) d) : Fin n → Fin d :=
  fun p => w (Fin.rev p, ⟨2 * r.val + 1, by omega⟩)

/-- Algorithm 3 with exact Schur transforms, `R` rounds and threshold `τ`, as an accept effect on
`2R` copies of each input state (published layout): in every round `r` the measurement
`{M_{λ,S}}` is performed on the forward block and on the reverse block; the effect is the sum,
over the outcome records `(S_r, S'_r)_r` that the classical post-processing accepts, of the
tensor product of the `2R` measured projectors. -/
noncomputable def alg3Effect (n d R : ℕ) (τ : ℝ) :
    Matrix (CopyBasis n (2 * R) d) (CopyBasis n (2 * R) d) ℂ :=
  fun v w =>
    ∑ o : Fin R → SchurOutcome n d × SchurOutcome n d,
      if alg3Accepts R τ o then
        ∏ r : Fin R, schurProj (d := d) (o r).1.val (forwardBlock r v) (forwardBlock r w) *
          schurProj (d := d) (o r).2.val (reverseBlock r v) (reverseBlock r w)
      else 0

/-- Sanity check: `P(J₁) = 0`. -/
example (n d : ℕ) : jmOp (n := n + 1) (d := d) 0 = 0 := by
  simp [jmOp]

end QuantumStateIdentity321.Schur.Supplement


