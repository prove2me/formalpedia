-- Prove2me | Definitions.Def_SymTensorNet_FewLegs
-- name    : SymTensorNet_FewLegs
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:19:15.192599+00:00
-- url     : https://prove2.me/theorems/ae5080c2-7d73-4635-8f7c-e0acc8b24e7c
-- title:
--   The three- and four-leg decompositions of Eqs. (10)–(12)
-- statement:
--   Fix fusion data for a catalogue of irreps of $G$.
--
--   1. **Three legs (Eq. (10)).** Legs $i,j$ are outgoing and leg $k$ incoming. For charges $a,b,c$ the channels of $a\otimes b$ with output $c$ index the structural tensors $(Q^{abc}_\kappa)_{m_an_bo_c}=(\iota_\kappa)_{(m_a,n_b),o_c}$, and a degeneracy family $P$ gives the tensor $T_{ijk}=\sum_\kappa(P^{abc}_\kappa)_{\alpha_a\beta_b\gamma_c}(Q^{abc}_\kappa)_{m_an_bo_c}$, where $i=(a,\alpha_a,m_a)$, $j=(b,\beta_b,n_b)$, $k=(c,\gamma_c,o_c)$.
--   2. **Four legs, first $a\otimes b$ (Eq. (11)).** Legs $i,j,k$ are outgoing and $l=(d,\delta_d,p_d)$ incoming. The coupled-basis labels $e$ are pairs $(\kappa_1,\kappa_2)$, $\kappa_1$ a channel of $a\otimes b$ and $\kappa_2$ a channel of $\mathrm{out}(\kappa_1)\otimes c$ with output $d$, and
--   $$(Q^{abcd}_e)_{m_an_bo_cp_d}=\sum_{q}(\iota_{\kappa_1})_{(m_a,n_b),q}(\iota_{\kappa_2})_{(q,o_c),p_d}.$$
--   A degeneracy family $P$ gives $T_{ijkl}=\sum_e(P^{abcd}_e)_{\alpha_a\beta_b\gamma_c\delta_d}(Q^{abcd}_e)_{m_an_bo_cp_d}$.
--   3. **Four legs, first $b\otimes c$ (Eq. (12)).** The labels $f$ are pairs $(\kappa_1,\kappa_2)$, $\kappa_1$ a channel of $b\otimes c$ and $\kappa_2$ a channel of $a\otimes\mathrm{out}(\kappa_1)$ with output $d$, and
--   $$(\tilde Q^{abcd}_f)_{m_an_bo_cp_d}=\sum_{r}(\iota_{\kappa_1})_{(n_b,o_c),r}(\iota_{\kappa_2})_{(m_a,r),p_d};$$
--   a family $\tilde P$ gives $T_{ijkl}=\sum_f(\tilde P^{abcd}_f)_{\alpha_a\beta_b\gamma_c\delta_d}(\tilde Q^{abcd}_f)_{m_an_bo_cp_d}$.
--
--   **Formalization Note** Legs are numbered $0,1,2$ (three legs) and $0,1,2,3$ (four legs). The intermediate indices $q_e$, $r_f$ are contracted inside the structural tensors and the degeneracy tensors carry no intermediate index $\epsilon_e$, $\zeta_f$. Beyond multiplicity freeness each fusion step is a channel (footnote [10]); when it holds, the label $e$ is the intermediate charge.
-- source:
--   Singh, Pfeifer & Vidal, Tensor network decompositions in the presence of a global symmetry, arXiv:0907.2994v2, Eq. (10), p.2; Eqs. (11), (12), p.3; footnote [10], p.4

import Mathlib
import Definitions.Def_SymTensorNet_SymmetricTensor
import Definitions.Def_SymTensorNet_FusionData

namespace SymTensorNet

universe u v

open Matrix

variable {G : Type u} [Group G]

/-- Leg directions of Eq. (10): legs `0, 1` (indices `i, j`) outgoing, leg `2` (index `k`)
incoming. arXiv:0907.2994v2, p.2: "two outgoing indices i, j and one incoming index k". -/
def dir3 : Fin 3 → Dir := ![Dir.out, Dir.out, Dir.inc]

/-- Leg directions of Eqs. (11)–(12): legs `0, 1, 2` (indices `i, j, k`) outgoing, leg `3` (index
`l`) incoming. arXiv:0907.2994v2, p.3: "three outgoing indices i, j and k and one incoming index
l = (d, δ_d, p_d)". -/
def dir4 : Fin 4 → Dir := ![Dir.out, Dir.out, Dir.out, Dir.inc]

/-- The fusion channels of `a ⊗ b` with output charge `c`: the copies of `𝕍^c` in `𝕍ᵃ ⊗ 𝕍ᵇ`
(one at most when `G` is multiplicity free). arXiv:0907.2994v2, p.2, Eq. (9), footnote [10]. -/
abbrev Chan10 (F : FusionData.{u, v} G) (a b c : F.Charge) : Type v :=
  {κ : F.Chan a b // F.out κ = c}

/-- The structural tensor of Eq. (10), the Clebsch–Gordan coefficients
`(Q^{abc})_{m_a n_b o_c} = (ι_κ)_{(m, n), o}` of the channel `κ`.
arXiv:0907.2994v2, p.2, Eq. (10). -/
def Q10 (F : FusionData.{u, v} G) {a b c : F.Charge} (κ : Chan10 F a b c) (m : Fin (F.dim a))
    (n : Fin (F.dim b)) (o : Fin (F.dim c)) : ℂ :=
  F.iso κ.1 (m, n) (Fin.cast (congrArg F.dim κ.2.symm) o)

/-- The three-leg synthesis of Eq. (10):
`T((α, m), (β, n), (γ, o)) = Σ_κ P(α, β, γ; κ) (Q^{abc}_κ)_{m n o}`, with `a, b, c` the charges of
`α, β, γ` and `κ` running over the channels of `a ⊗ b` with output `c`.
arXiv:0907.2994v2, p.2, Eq. (10): `(T)_{ijk} = (P^{abc})_{α_a β_b γ_c} (Q^{abc})_{m_a n_b o_c}`. -/
def synth10 (F : FusionData.{u, v} G) {Deg : Fin 3 → Type*} (chg : (s : Fin 3) → Deg s → F.Charge)
    (P : (α : (s : Fin 3) → Deg s) → Chan10 F (chg 0 (α 0)) (chg 1 (α 1)) (chg 2 (α 2)) → ℂ) :
    ((s : Fin 3) → LegIdx F.toIrrepCatalogue chg s) → ℂ :=
  fun i => ∑ κ : Chan10 F (chg 0 (i 0).1) (chg 1 (i 1).1) (chg 2 (i 2).1),
    P (fun s => (i s).1) κ * Q10 F κ (i 0).2 (i 1).2 (i 2).2

/-- The labels of the coupled basis `|d p_d; e⟩` of Eq. (11): first `a` and `b` fuse into `e`
(channel `κ₁`), then `e` and `c` fuse into `d` (channel `κ₂`).
arXiv:0907.2994v2, p.3: "Let e be the charge that results from fusing a and b". -/
abbrev Lab11 (F : FusionData.{u, v} G) (a b c d : F.Charge) : Type v :=
  {e : Σ κ₁ : F.Chan a b, F.Chan (F.out κ₁) c // F.out e.2 = d}

/-- The structural tensor of Eq. (11), the change of basis to the coupled basis `|d p_d; e⟩`:
`(Q^{abcd}_e)_{m n o p} = Σ_q (ι_{κ₁})_{(m, n), q} (ι_{κ₂})_{(q, o), p}`.
arXiv:0907.2994v2, p.3, Eq. (11).

**Formalization Note** The intermediate index `q_e` is contracted inside `Q` and the intermediate
degeneracy index `ϵ_e` is not an index of `P` (see `structQ`). -/
def Q11 (F : FusionData.{u, v} G) {a b c d : F.Charge} (e : Lab11 F a b c d) (m : Fin (F.dim a))
    (n : Fin (F.dim b)) (o : Fin (F.dim c)) (p : Fin (F.dim d)) : ℂ :=
  ∑ q : Fin (F.dim (F.out e.1.1)),
    F.iso e.1.1 (m, n) q * F.iso e.1.2 (q, o) (Fin.cast (congrArg F.dim e.2.symm) p)

/-- The four-leg synthesis of Eq. (11):
`T((α, m), (β, n), (γ, o), (δ, p)) = Σ_e P(α, β, γ, δ; e) (Q^{abcd}_e)_{m n o p}`.
arXiv:0907.2994v2, p.3, Eq. (11). -/
def synth11 (F : FusionData.{u, v} G) {Deg : Fin 4 → Type*} (chg : (s : Fin 4) → Deg s → F.Charge)
    (P : (α : (s : Fin 4) → Deg s) →
      Lab11 F (chg 0 (α 0)) (chg 1 (α 1)) (chg 2 (α 2)) (chg 3 (α 3)) → ℂ) :
    ((s : Fin 4) → LegIdx F.toIrrepCatalogue chg s) → ℂ :=
  fun i => ∑ e : Lab11 F (chg 0 (i 0).1) (chg 1 (i 1).1) (chg 2 (i 2).1) (chg 3 (i 3).1),
    P (fun s => (i s).1) e * Q11 F e (i 0).2 (i 1).2 (i 2).2 (i 3).2

/-- The labels of the coupled basis `|d p_d; f⟩` of Eq. (12): first `b` and `c` fuse into `f`
(channel `κ₁`), then `a` and `f` fuse into `d` (channel `κ₂`).
arXiv:0907.2994v2, p.3: "obtained by fusing first b and c into f, and then a and f into d". -/
abbrev Lab12 (F : FusionData.{u, v} G) (a b c d : F.Charge) : Type v :=
  {f : Σ κ₁ : F.Chan b c, F.Chan a (F.out κ₁) // F.out f.2 = d}

/-- The structural tensor of Eq. (12):
`(Q̃^{abcd}_f)_{m n o p} = Σ_r (ι_{κ₁})_{(n, o), r} (ι_{κ₂})_{(m, r), p}`.
arXiv:0907.2994v2, p.3, Eq. (12). -/
def Q12 (F : FusionData.{u, v} G) {a b c d : F.Charge} (f : Lab12 F a b c d) (m : Fin (F.dim a))
    (n : Fin (F.dim b)) (o : Fin (F.dim c)) (p : Fin (F.dim d)) : ℂ :=
  ∑ r : Fin (F.dim (F.out f.1.1)),
    F.iso f.1.1 (n, o) r * F.iso f.1.2 (m, r) (Fin.cast (congrArg F.dim f.2.symm) p)

/-- The four-leg synthesis of Eq. (12):
`T((α, m), (β, n), (γ, o), (δ, p)) = Σ_f P̃(α, β, γ, δ; f) (Q̃^{abcd}_f)_{m n o p}`.
arXiv:0907.2994v2, p.3, Eq. (12). -/
def synth12 (F : FusionData.{u, v} G) {Deg : Fin 4 → Type*} (chg : (s : Fin 4) → Deg s → F.Charge)
    (P : (α : (s : Fin 4) → Deg s) →
      Lab12 F (chg 0 (α 0)) (chg 1 (α 1)) (chg 2 (α 2)) (chg 3 (α 3)) → ℂ) :
    ((s : Fin 4) → LegIdx F.toIrrepCatalogue chg s) → ℂ :=
  fun i => ∑ f : Lab12 F (chg 0 (i 0).1) (chg 1 (i 1).1) (chg 2 (i 2).1) (chg 3 (i 3).1),
    P (fun s => (i s).1) f * Q12 F f (i 0).2 (i 1).2 (i 2).2 (i 3).2

end SymTensorNet


