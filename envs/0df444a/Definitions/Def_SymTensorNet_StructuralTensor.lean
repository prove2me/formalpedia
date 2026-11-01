-- Prove2me | Definitions.Def_SymTensorNet_StructuralTensor
-- name    : SymTensorNet_StructuralTensor
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:20:31.153983+00:00
-- url     : https://prove2.me/theorems/2405813e-d7ad-48e3-bfe7-7d9fc66d2f61
-- title:
--   The structural tensors $Q(a,\ell)$ of a trivalent tree and the synthesis map $P\mapsto T$ of Eq. (15)
-- statement:
--   Fix fusion data and conjugation data ($\bar a$, $J^a$) for a catalogue of irreps of $G$, a finite set $S$ of legs with directions, a root leg $r$ and a fusion tree $\tau$ valid for $r$.
--
--   For leg charges $a=(a_s)_s$, a leg enters the tree with charge $x_s=a_s$ if it is outgoing and $x_s=\bar a_s$ if it is incoming. The tree must fuse into the **root charge** $c_r=a_r$ if $r$ is incoming and $c_r=\bar a_r$ if $r$ is outgoing. The **admissible labellings** $L(\tau,r,a)$ are the labellings of $\tau$ (leaf charges $x$) whose top charge is $c_r$: they are the allowed values of the intermediate charges $e_1,\dots,e_{t'}$.
--
--   For $\ell\in L(\tau,r,a)$ the **structural tensor** is
--   $$Q(a,\ell)_{m}=\sum_{o}A(\tau,\ell)(m,o)\,\rho_{o,m_r},$$
--   where $A$ is the tree amplitude with leaf matrix the identity on outgoing legs and $\overline{J^{a_s}}$ on incoming legs, and $\rho$ is the identity if $r$ is incoming and $J^{a_r}$ if $r$ is outgoing. It depends only on the symmetry data, the directions, the charges and the tree. With the root incoming and every other leg outgoing it is the paper's $Q$: $\delta_{ab}\delta_{m_an_b}$ for two legs (Eq. (8)), the Clebsch–Gordan coefficients for three legs (Eq. (10)), and $\sum_qQ^{abe}_{m_an_bq}Q^{ecd}_{qo_cp_d}$ for four legs (Eq. (11)).
--
--   A **degeneracy family** $P$ assigns a complex number $P(\alpha,\ell)$ to every choice of degeneracy labels $\alpha=(\alpha_s)_s$ (with charges $a_s=\mathrm{chg}_s(\alpha_s)$) and every $\ell\in L(\tau,r,a)$, with no constraint. Its **synthesis** is the tensor
--   $$T_{(\alpha_s,m_s)_s}=\sum_{\ell\in L(\tau,r,a)}P(\alpha,\ell)\,Q(a,\ell)_m .$$
--   This is the right-hand side of Eq. (15).
--
--   **Formalization Note** The intermediate index $m_{e_k}$ of Eq. (15) (the $q_e$ of Eq. (11), the $r_f$ of Eq. (12)) is contracted inside $Q$, and the intermediate degeneracy index $\alpha_{e_k}$ ($\epsilon_e$, $\zeta_f$) is not an index of $P$: below Eq. (12) the paper writes $(\tilde Q^{abcd}_f)_{m_an_bo_cp_d}$ without $r_f$, the coupled basis $|dp_d;e\rangle$ of Eq. (11) carries no $q_e$, and in Fig. 2(iv) only the structural part carries the inner edge.
-- source:
--   Singh, Pfeifer & Vidal, Tensor network decompositions in the presence of a global symmetry, arXiv:0907.2994v2, Eq. (15), p.3; Eqs. (8), (10), p.2; Eqs. (11), (12), p.3; Fig. 2(iv), p.3

import Mathlib
import Definitions.Def_SymTensorNet_SymmetricTensor
import Definitions.Def_SymTensorNet_FusionTree

namespace SymTensorNet

universe u v w

open Matrix

variable {G : Type u} [Group G]

/-- The charge with which a leg of direction `d` and charge `a` enters a fusion tree: `a` for an
outgoing leg, `ā` for an incoming one.

arXiv:0907.2994v2, p.3, Eq. (15): "intertwining operators between the tensor products of incoming
and outgoing irreps". -/
def dirCharge {C : IrrepCatalogue.{u, v} G} (K : ConjData C) : Dir → C.Charge → C.Charge
  | .out, a => a
  | .inc, a => K.conj a

/-- The leaf matrix of a leg of direction `d` and charge `a`, from `𝕍^{dirCharge d a}` to the leg's
basis index `m ∈ Fin (dim a)`: the identity for an outgoing leg, `conj(Jᵃ)` for an incoming leg. -/
def legMap {C : IrrepCatalogue.{u, v} G} (K : ConjData C) :
    (d : Dir) → (a : C.Charge) → Matrix (Fin (C.dim (dirCharge K d a))) (Fin (C.dim a)) ℂ
  | .out, a => (1 : Matrix (Fin (C.dim a)) (Fin (C.dim a)) ℂ)
  | .inc, a => (K.J a).map star

/-- The charge into which the tree must fuse for a root leg of direction `d` and charge `a`: `a`
for an incoming root, `ā` for an outgoing root. -/
def rootCharge {C : IrrepCatalogue.{u, v} G} (K : ConjData C) : Dir → C.Charge → C.Charge
  | .inc, a => a
  | .out, a => K.conj a

/-- The root matrix, from the top irrep `𝕍^{rootCharge d a}` to the root leg's basis index: the
identity for an incoming root, `Jᵃ` for an outgoing root. -/
def rootMap {C : IrrepCatalogue.{u, v} G} (K : ConjData C) :
    (d : Dir) → (a : C.Charge) → Matrix (Fin (C.dim (rootCharge K d a))) (Fin (C.dim a)) ℂ
  | .inc, a => (1 : Matrix (Fin (C.dim a)) (Fin (C.dim a)) ℂ)
  | .out, a => K.J a

/-- The charges at the leaves of the tree, for leg charges `a`: `x_s = a_s` on an outgoing leg and
`x_s = ā_s` on an incoming leg. -/
def leafCharge (F : FusionData.{u, v} G) (K : ConjData F.toIrrepCatalogue) {S : Type w}
    (dir : S → Dir) (a : S → F.Charge) : S → F.Charge :=
  fun s => dirCharge K (dir s) (a s)

/-- The **admissible labellings** `L(τ, r, a)` of the tree `τ` for leg charges `a` and root `r`:
the labellings whose top charge is the root charge (`a_r` if `r` is incoming, `ā_r` if outgoing).
These are the values of the intermediate charges `e₁, …, e_{t′}` (and multiplicity indices)
allowed in the sum of Eq. (15).

arXiv:0907.2994v2, p.3, Eq. (15). -/
abbrev AdmLab (F : FusionData.{u, v} G) (K : ConjData F.toIrrepCatalogue) {S : Type w}
    (dir : S → Dir) (τ : Tree S) (r : S) (a : S → F.Charge) : Type v :=
  {ℓ : Lab F (leafCharge F K dir a) τ // top F (leafCharge F K dir a) τ ℓ = rootCharge K (dir r) (a r)}

/-- The **structural tensor** `Q(a, ℓ)(m)` of Eq. (15) for leg charges `a`, an admissible labelling
`ℓ` of the tree `τ`, and basis indices `m_s ∈ Fin (dim a_s)`:
`Q(a, ℓ)(m) = Σ_o A(τ, ℓ)(m, o) · ρ(o, m_r)`, where `A` is the tree amplitude with leaf matrices
`legMap` (identity on outgoing legs, `conj(J)` on incoming legs) and `ρ = rootMap` (identity for an
incoming root, `J` for an outgoing root). It depends only on the fusion data, the directions, the
charges and the tree: never on the degeneracy spaces or on a tensor.

With the root incoming and all other legs outgoing this is the paper's `Q`: `δ_{ab} δ_{m n}` for
`t = 2` (Eq. (8)), the Clebsch–Gordan coefficients for `t = 3` (Eq. (10)), and the double fusion
`Σ_q Q^{abe}_{m n q} Q^{ecd}_{q o p}` for `t = 4` (Eq. (11)).

arXiv:0907.2994v2, p.3, Eq. (15): "the structural tensors Q^{a₁…a_t}_{e₁…e_{t′}} are completely
determined by the symmetry".

**Formalization Note** The intermediate index `m_{e_k}` (the paper's `q_e`, `r_f`) is contracted
inside `Q`, and the paper's `α_{e_k}` (`ϵ_e`, `ζ_f`) is not an index: intermediate branches carry
no degeneracy space. Evidence: below Eq. (12) `Q̃` is written without `r_f`; the coupled basis
`|d p_d; e⟩` of Eq. (11) carries no `q_e`; Fig. 2(iv). -/
def structQ (F : FusionData.{u, v} G) (K : ConjData F.toIrrepCatalogue) {S : Type w}
    (dir : S → Dir) (τ : Tree S) (r : S) (a : S → F.Charge) (ℓ : AdmLab F K dir τ r a)
    (m : (s : S) → Fin (F.dim (a s))) : ℂ :=
  ∑ o : Fin (F.dim (rootCharge K (dir r) (a r))),
    treeAmp F (leafCharge F K dir a) (fun s => legMap K (dir s) (a s)) τ ℓ.1 m
        (Fin.cast (congrArg F.dim ℓ.2.symm) o) *
      rootMap K (dir r) (a r) o (m r)

/-- The **synthesis map** of Eq. (15): a degeneracy family `P`, which assigns to every choice of
degeneracy labels `α` (hence of charges `a_s = chg s (α s)`) and every admissible labelling `ℓ` an
unconstrained number `P(α, ℓ)`, gives the tensor
`T((α_s, m_s)_s) = Σ_{ℓ ∈ L(τ, r, a)} P(α, ℓ) Q(a, ℓ)(m)`.

arXiv:0907.2994v2, p.3, Eq. (15):
`(T)_{i₁…i_t} = Σ (P^{a₁…a_t}_{e₁…e_{t′}})_{α…} × (Q^{a₁…a_t}_{e₁…e_{t′}})_{m…}`. -/
def synth (F : FusionData.{u, v} G) (K : ConjData F.toIrrepCatalogue) {S : Type w}
    (dir : S → Dir) (τ : Tree S) (r : S) {Deg : S → Type*} (chg : (s : S) → Deg s → F.Charge)
    (P : (α : (s : S) → Deg s) → AdmLab F K dir τ r (fun s => chg s (α s)) → ℂ) :
    ((s : S) → LegIdx F.toIrrepCatalogue chg s) → ℂ :=
  fun i => ∑ ℓ : AdmLab F K dir τ r (fun s => chg s (i s).1),
    P (fun s => (i s).1) ℓ * structQ F K dir τ r (fun s => chg s (i s).1) ℓ (fun s => (i s).2)

end SymTensorNet


