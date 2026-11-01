-- Prove2me | Definitions.Def_SymTensorNet_SymmetricTensor
-- name    : SymTensorNet_SymmetricTensor
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:18:29.224297+00:00
-- url     : https://prove2.me/theorems/a345cbb8-37e9-4607-918b-f2da8ede94c3
-- title:
--   Tensor legs with directions and degeneracy spaces, the action of $G$ on them, and symmetric tensors
-- statement:
--   Fix a catalogue of irreps $U^a$ of a group $G$. A tensor $T$ has a finite set $S$ of **legs** (indices). Each leg $s$ has a **direction**, outgoing or incoming, and a vector space that decomposes as in Eq. (4),
--   $$\bigoplus_a \big(\mathbb D^a_s\otimes\mathbb V^a\big),$$
--   with a finite-dimensional **degeneracy space** $\mathbb D^a_s$ for each charge $a$ (possibly zero, and nonzero for finitely many $a$). Its basis vectors are $i=(a,\alpha_a,m_a)$: $\alpha_a$ labels a basis vector of $\mathbb D^a_s$ and $m_a$ a basis vector of $\mathbb V^a$.
--
--   The group acts on leg $s$ by the block-diagonal unitary of Eq. (5),
--   $$R^s_g=\bigoplus_a\big(\mathbb I^a\otimes U^a_g\big)$$
--   on an outgoing leg, and by its entrywise complex conjugate on an incoming leg. A tensor $T$ is **symmetric** when it is invariant under the simultaneous action of $G$ on all its legs:
--   $$\sum_{j}\Big(\prod_{s\in S}(R^s_g)_{i_s j_s}\Big)\,T_{j}=T_{i}\qquad\text{for all }g\in G\text{ and all indices }i=(i_s)_{s\in S}.$$
--
--   For two outgoing legs $i,j$ and one incoming leg $k$ this is Eq. (7), $\sum_{ijk}(U_g)_{i'i}(V_g)_{j'j}T_{ijk}(W^\dagger_g)_{kk'}=T_{i'j'k'}$, since $(W^\dagger_g)_{kk'}=\overline{(W_g)_{k'k}}$.
--
--   **Formalization Note** The degeneracy labels of a leg form one finite set $\mathrm{Deg}_s$, each label $\alpha$ carrying a charge $\mathrm{chg}_s(\alpha)$; so $\mathbb D^a_s$ has basis $\{\alpha:\mathrm{chg}_s(\alpha)=a\}$ and a basis index of leg $s$ is a pair $(\alpha,m)$ with $m\in\{1,\dots,\dim\mathrm{chg}_s(\alpha)\}$. Different legs have different degeneracy spaces and share one catalogue.
-- source:
--   Singh, Pfeifer & Vidal, Tensor network decompositions in the presence of a global symmetry, arXiv:0907.2994v2, Eqs. (4), (5), (7) and "we can write i = (a, α_a, m_a)", p.2

import Mathlib
import Definitions.Def_SymTensorNet_IrrepCatalogue

namespace SymTensorNet

open Matrix

/-- The direction of a tensor leg: **outgoing** or **incoming**.

arXiv:0907.2994v2, p.2, Eq. (7): "two outgoing indices i and j and one incoming index k". -/
inductive Dir
  | out
  | inc
  deriving DecidableEq

variable {G : Type*} [Group G]

/-- The matrix by which `g` acts on the irrep block of charge `a` of a leg of direction `d`:
`Uᵃ_g` on an outgoing leg and its entrywise complex conjugate `conj(Uᵃ_g)` on an incoming leg.

arXiv:0907.2994v2, p.2, Eq. (7): an incoming index `k` is contracted with `(W†_g)_{kk′}`, and
`Σ_k T_k (W†_g)_{kk′} = Σ_k conj((W_g)_{k′k}) T_k`, so an incoming leg is acted on from the left
by the entrywise conjugate. -/
def legRep (C : IrrepCatalogue G) (d : Dir) (a : C.Charge) (g : G) :
    Matrix (Fin (C.dim a)) (Fin (C.dim a)) ℂ :=
  match d with
  | .out => (C.rep a g : Matrix (Fin (C.dim a)) (Fin (C.dim a)) ℂ)
  | .inc => (C.rep a g : Matrix (Fin (C.dim a)) (Fin (C.dim a)) ℂ).map star

/-- The index set of leg `s`: pairs `(α, m)` with `α ∈ Deg s` a degeneracy label carrying the
charge `chg s α`, and `m ∈ Fin (dim (chg s α))` a basis index inside that irrep. The degeneracy
space `𝔻ᵃ` of charge `a` on leg `s` is `{α ∈ Deg s | chg s α = a}`.

arXiv:0907.2994v2, p.2: "we can write i = (a, α_a, m_a)" and Eq. (4)
`𝕍 ≅ ⊕_a (𝔻ᵃ ⊗ 𝕍ᵃ)`. -/
abbrev LegIdx (C : IrrepCatalogue G) {S : Type*} {Deg : S → Type*}
    (chg : (s : S) → Deg s → C.Charge) (s : S) : Type _ :=
  Σ α : Deg s, Fin (C.dim (chg s α))

/-- The unitary matrix by which `g` acts on leg `s`, block diagonal as in Eq. (5):
`R^s_g = ⊕_a (𝕀ᵃ ⊗ Uᵃ_g)` on an outgoing leg and its entrywise conjugate on an incoming one.

arXiv:0907.2994v2, p.2, Eq. (5), with Eq. (7) for incoming legs. -/
def legMatrix (C : IrrepCatalogue G) {S : Type*} (dir : S → Dir) {Deg : S → Type*}
    [∀ s, DecidableEq (Deg s)] (chg : (s : S) → Deg s → C.Charge) (s : S) (g : G) :
    Matrix (LegIdx C chg s) (LegIdx C chg s) ℂ :=
  Matrix.blockDiagonal' (fun α : Deg s => legRep C (dir s) (chg s α) g)

/-- A tensor `T` with legs `S` is **symmetric** when it is invariant under the simultaneous action
of `G` on all its legs:
`Σ_j (∏_s (R^s_g)_{i_s j_s}) T_j = T_i` for all `g` and all indices `i`.

arXiv:0907.2994v2, p.2, Eq. (7): "tensors that are invariant under the simultaneous action of G
on all their indices".

**Formalization Note** Each leg has its own degeneracy spaces (Eq. (7) uses different
representations `U, V, W` on different legs); all legs share one catalogue of irreps. Degeneracy
spaces may be empty, and only finitely many are nonempty on each leg (`Deg s` is finite). -/
def IsSymmetric (C : IrrepCatalogue G) {S : Type*} [Fintype S] [DecidableEq S] (dir : S → Dir)
    {Deg : S → Type*} [∀ s, Fintype (Deg s)] [∀ s, DecidableEq (Deg s)]
    (chg : (s : S) → Deg s → C.Charge) (T : ((s : S) → LegIdx C chg s) → ℂ) : Prop :=
  ∀ (g : G) (i : (s : S) → LegIdx C chg s),
    ∑ j : (s : S) → LegIdx C chg s, (∏ s, legMatrix C dir chg s g (i s) (j s)) * T j = T i

end SymTensorNet


