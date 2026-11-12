-- Prove2me | Definitions.Def_QubitTracking_anchorVec
-- name    : QubitTracking_anchorVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:27:45.030501+00:00
-- url     : https://prove2.me/theorems/454fc839-fc1c-4fbf-b246-36b73f39d418
-- title:
--   The quantum anchor state $|\Psi^{\mathsf{sk}}_{n_e,n_h,n_s}\rangle$
-- statement:
--   Let $d=n_h+n_e+n_s$ and let $U=U_{\mathsf{shift}}\in GL_d(\mathbb F_2)$ be a change of basis. The subspace $S$ is spanned by the first $n_h$ columns of $U$ and $T$ by the first $n_h+n_e$ columns; $S^\perp=\{z:\langle z,s\rangle=0\ \forall s\in S\}$. For $u'\in\mathbb F_2^{n_h}$ and $v'\in\mathbb F_2^{n_s}$ put
--   $$u=U^{-t}(u'\times 0^{n_e+n_s}),\qquad v=U(0^{n_h+n_e}\times v').$$
--   The **anchor state** on an $n_e$-qubit anchor register $\mathbf A$ and a $d$-qubit vessel register $\mathbf B$ is
--   $$|\Psi^{\mathsf{sk}}_{n_e,n_h,n_s}\rangle=2^{-(n_e+n_h)/2}\sum_{x\in\mathbb F_2^{n_e}}|x\rangle_{\mathbf A}\sum_{s\in S}(-1)^{\langle s,u\rangle}\,|s+U(0^{n_h}\times x\times 0^{n_s})+v\rangle_{\mathbf B},$$
--   with secret key $\mathsf{sk}=(U_{\mathsf{shift}},u,v)$. Sampling $U$, $u'$, $v'$ uniformly is $\mathsf{GenAnchorState}_{n_e,n_h,n_s}(1^\lambda)$.
--
--   The anchor register holds $n_e$ EPR halves whose partners are hidden in the vessel by the random change of basis; this state is the object every protocol of the paper localizes.
--
--   **Formalization Note** The paper generates the state by preparing $d$ EPR pairs, measuring $n_h$ of them in the Hadamard basis (outcome $u'$) and $n_s$ in the standard basis (outcome $v'$), and applying $U_{\mathsf{shift}}$ to the vessel; the closed form is the normalized post-measurement state displayed on p.27. Uniform $(U,u',v')$ reproduces the generation procedure.
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), Remark 4.1 (p.26), Definition 4.2 (pp.26–27)

import Definitions.Def_QubitTracking_Bits

set_option autoImplicit false

open Matrix

namespace QubitTracking

/-- The block vector `a × b × c ∈ 𝔽₂^d` with its first `nh` coordinates `a`, the next `ne`
coordinates `b` and the next `ns` coordinates `c` (p.26: "`0^n × x` denotes a vector … with its
first `n` bits all zeros and its last `n` bits being `x`"). Coordinates beyond `nh + ne + ns` are
`0`; every use has `d = nh + ne + ns`. -/
def blk {d nh ne ns : ℕ} (a : Bits (Fin nh)) (b : Bits (Fin ne)) (c : Bits (Fin ns)) :
    Bits (Fin d) :=
  fun i =>
    if h1 : (i : ℕ) < nh then a ⟨i, h1⟩
    else if h2 : (i : ℕ) < nh + ne then b ⟨(i : ℕ) - nh, by omega⟩
    else if h3 : (i : ℕ) - nh - ne < ns then c ⟨(i : ℕ) - nh - ne, h3⟩
    else 0

/-- The subspace of `𝔽₂^d` spanned by the first `k` columns of the change-of-basis matrix `U`
(Remark 4.1, p.26: subspaces are described by columns of an invertible matrix). -/
def colSpan {d : ℕ} (U : GL (Fin d) (ZMod 2)) (k : ℕ) : Submodule (ZMod 2) (Bits (Fin d)) :=
  Submodule.span (ZMod 2)
    {x | ∃ j : Fin d, (j : ℕ) < k ∧ x = fun i => (U : Matrix (Fin d) (Fin d) (ZMod 2)) i j}

/-- The dual subspace `S^⊥ = {z ∈ 𝔽₂^d : ⟨z, s⟩ = 0 for all s ∈ S}` (dot product over `𝔽₂`). -/
def perp {d : ℕ} (S : Submodule (ZMod 2) (Bits (Fin d))) : Submodule (ZMod 2) (Bits (Fin d)) where
  carrier := {z | ∀ s ∈ S, z ⬝ᵥ s = 0}
  add_mem' := by
    intro a b ha hb s hs
    simp [add_dotProduct, ha s hs, hb s hs]
  zero_mem' := by
    intro s _
    simp
  smul_mem' := by
    intro c z hz s hs
    simp [smul_dotProduct, hz s hs]

/-- The subspace `S` of the anchor state (Definition 4.2, p.26): spanned by the first `n_h`
columns of `U_shift`. -/
def anchorS {d : ℕ} (nh : ℕ) (U : GL (Fin d) (ZMod 2)) : Submodule (ZMod 2) (Bits (Fin d)) :=
  colSpan U nh

/-- The subspace `T` of the anchor state (Definition 4.2, p.26): spanned by the first
`n_h + n_e` columns of `U_shift`. -/
def anchorT {d : ℕ} (nh ne : ℕ) (U : GL (Fin d) (ZMod 2)) : Submodule (ZMod 2) (Bits (Fin d)) :=
  colSpan U (nh + ne)

/-- The shift `u = U_shift^{-t}(u′ × 0^{n_e+n_s})` of the anchor state (Definition 4.2, step 2,
p.26), where `U^{-t} = (U^t)^{-1} = (U^{-1})^t`. -/
def anchorU {d : ℕ} (nh ne ns : ℕ) (U : GL (Fin d) (ZMod 2)) (u' : Bits (Fin nh)) :
    Bits (Fin d) :=
  ((↑U⁻¹ : Matrix (Fin d) (Fin d) (ZMod 2))ᵀ) *ᵥ blk (ne := ne) (ns := ns) u' 0 0

/-- The shift `v = U_shift(0^{n_h+n_e} × v′)` of the anchor state (Definition 4.2, step 2,
p.26). -/
def anchorV {d : ℕ} (nh ne ns : ℕ) (U : GL (Fin d) (ZMod 2)) (v' : Bits (Fin ns)) :
    Bits (Fin d) :=
  (U : Matrix (Fin d) (Fin d) (ZMod 2)) *ᵥ blk (nh := nh) (ne := ne) 0 0 v'

open Classical in
/-- **The quantum anchor state** `|Ψ^{sk}_{n_e,n_h,n_s}⟩` (Definition 4.2, pp.26–27), on an
`n_e`-qubit anchor register `𝐀` and a `d = n_h + n_e + n_s`-qubit vessel register `𝐁`, for the
secret key `sk = (U_shift, u, v)` determined by the change of basis `U = U_shift`, the Hadamard
outcome `u′ ∈ 𝔽₂^{n_h}` and the standard outcome `v′ ∈ 𝔽₂^{n_s}`. Its amplitudes are the
closed form displayed on p.27,
`|Ψ^{sk}⟩ = 2^{-(n_e+n_h)/2} ∑_{x ∈ 𝔽₂^{n_e}} |x⟩_𝐀 ∑_{s ∈ S} (−1)^{⟨s,u⟩} |s + U(0^{n_h} × x × 0^{n_s}) + v⟩_𝐁`:
the amplitude of `|x⟩|b⟩` is `2^{-(n_e+n_h)/2} (−1)^{⟨s,u⟩}` if
`s := b − U(0^{n_h} × x × 0^{n_s}) − v` lies in `S`, and `0` otherwise.

**Formalization Note** The paper generates the state by preparing `n_h + n_e + n_s` EPR pairs,
measuring `𝐔` in the Hadamard basis (outcome `u′`) and `𝐕` in the standard basis (outcome `v′`),
each outcome having probability `2^{-n_h}`, `2^{-n_s}`, and applying `U_shift` to the vessel. The
closed form is that post-measurement state, normalized (`2^{n_e}` branches, each with `|S| = 2^{n_h}`
basis vectors of equal amplitude). Sampling `U`, `u′`, `v′` uniformly reproduces `GenAnchorState`. -/
noncomputable def anchorVec (ne nh ns : ℕ) {d : ℕ} (U : GL (Fin d) (ZMod 2))
    (u' : Bits (Fin nh)) (v' : Bits (Fin ns)) : Bits (Fin ne) × Bits (Fin d) → ℂ :=
  fun p =>
    let s : Bits (Fin d) :=
      p.2 - (U : Matrix (Fin d) (Fin d) (ZMod 2)) *ᵥ blk (nh := nh) (ns := ns) 0 p.1 0
        - anchorV nh ne ns U v'
    if s ∈ anchorS nh U then
      ((Real.sqrt 2 : ℂ) ^ (ne + nh))⁻¹ * sgn (s ⬝ᵥ anchorU nh ne ns U u')
    else 0

end QubitTracking


