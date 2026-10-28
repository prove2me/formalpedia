-- Prove2me | Definitions.Def_NonAbelianDMNRG_Recursion_Multiplets
-- name    : NonAbelianDMNRG_Recursion_Multiplets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T09:28:28.388543+00:00
-- url     : https://prove2.me/theorems/e6ab8af6-f3de-41cb-8806-64dafc808bf5
-- title:
--   Labelled irreducible multiplets, block and site spaces, the symmetry action $U(g)=V(g)\otimes L(g)$ and the canonical basis (21) (pp. 3–4, 7)
-- statement:
--   This file fixes the symmetry setting of one iteration of Wilson's numerical renormalization group (NRG) in the presence of a (possibly non-Abelian) symmetry group, following Tóth, Moca, Legeza and Zaránd, §II.B–C and §III.
--
--   **Labels and multiplets.** A symmetry group $G$ acts on every multiplet through a labelled unitary representation. Each label $Q$ (a representation index) has a dimension $\dim Q$ and a homomorphism $\pi_Q : G \to U(\dim Q)$ into the unitary $\dim Q\times\dim Q$ matrices; the internal quantum number $Q^z$ runs over $\{0,\dots,\dim Q-1\}$. The associated linear representation of $G$ on $\mathbb C^{\dim Q}$ is `labelRep`.
--
--   A space built from multiplets $i\in I$ with labels $Q_i$ has the orthonormal basis $|i, Q^z\rangle$, $Q^z<\dim Q_i$ (the type `Multiplets dim Qi`), and $G$ acts on it by the block-diagonal unitary
--   $$
--   \bigoplus_{i\in I}\pi_{Q_i}(g)
--   $$
--   (`multipletRep`). For the kept multiplets $u\in K$ of iteration $n-1$ (the block, or old, states) this is the paper's $V(g)$; for the local multiplets $\mu\in\Lambda$ of site $n$ it is $L(g)$.
--
--   **The new space.** The states of iteration $n$ are built from block and local states: the basis is $|u, Q^z_u;\mu, q^z_\mu\rangle$, indexed block first, and the symmetry acts by
--   $$
--   U(g) = V(g)\otimes L(g)
--   $$
--   (`newRep`), the locality property $U(g)\equiv L(g)V(g)$ of p. 7.
--
--   **Canonical basis (21).** A coupling rule assigns to labels $q, Q$ a finite set of labels $Q'$ occurring in $q\otimes Q$, and the generalized Clebsch–Gordan coefficients are matrices $C_{qQ}^{Q'}$ with entries $\langle q\, q^z; Q\, Q^z \mid Q'\, Q'^z\rangle$, rows indexed local first. A canonical multiplet $\tilde\imath = ((u,\mu), Q_{\tilde\imath})$ consists of a kept multiplet $u$, a local multiplet $\mu$ and a label $Q_{\tilde\imath}$ in the coupling set of $(q_\mu, Q_u)$ (`Can`). Its states are
--   $$
--   |\tilde\imath, Q_{\tilde\imath}, Q^z_{\tilde\imath}\rangle = \sum_{Q^z_u,\,q^z_\mu} \langle q_\mu q^z_\mu; Q_u Q^z_u \mid Q_{\tilde\imath} Q^z_{\tilde\imath}\rangle\, |u, Q_u, Q^z_u; \mu, q_\mu, q^z_\mu\rangle ,
--   $$
--   and `canonicalBasis` is the matrix whose columns are these vectors.
--
--   **Iteration $n-1$.** The space of iteration $n-1$ has the discarded multiplets $d\in D$ followed by the kept ones; `prevRep` is the block-diagonal symmetry action on it, and `truncatedOperator` is the operator of (39): the weighted projection $\sum_{i\in D} w_i \sum_{Q^z}|i, Q_i, Q^z\rangle\langle i, Q_i, Q^z|$ on the discarded multiplets plus a given operator on the kept ones.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The paper's product group $G_1\times\dots\times G_\Gamma$ with label vectors $\underline Q$ is replaced by one abstract group with labelled representations; the product case is an instance, with the generalized Clebsch–Gordan coefficients of p. 4 as products. The coupling is multiplicity-free: one coefficient array per label triple, as (21) is written. Operators on the new space are indexed block first (matching the partial trace over the right factor), Clebsch–Gordan matrices local first. No fermionic sign factors appear: the space is the plain tensor product in the ordering of (21). The coefficient matrices are given for every label triple; only those in the coupling set enter the canonical basis.
-- source:
--   Tóth, Moca, Legeza, Zaránd, Density matrix numerical renormalization group for non-Abelian symmetries, arXiv:0802.4332v1, pp. 3–4, eqs. (16)–(21); p. 7, eqs. (39)–(40)

import Mathlib
import Definitions.Def_WildeQIT_partialTrace

namespace NonAbelianDMNRG.Recursion

open Matrix
open scoped Kronecker

/-!
Tóth, Moca, Legeza, Zaránd, *Density matrix numerical renormalization group for non-Abelian
symmetries*, arXiv:0802.4332v1, pp. 3–4, eqs. (16)–(21).

The symmetry group `G` acts on every multiplet through a labelled unitary irreducible
representation: a label `Q : Lab` has dimension `dim Q` and a unitary matrix representation
`π Q : G →* unitaryGroup (Fin (dim Q)) ℂ`. A space built from multiplets `i : I` carrying labels
`Qi i` has the basis `Σ i, Fin (dim (Qi i))` (multiplet `i`, internal quantum number `Q^z`), and
`G` acts on it block-diagonally. The new space of an NRG iteration is (block states) × (local
states), indexed block first; generalized Clebsch–Gordan matrices `cg q Q Q'` are indexed local
first, `((q^z, Q^z), Q'^z) ↦ ⟨q q^z; Q Q^z | Q' Q'^z⟩`, as in (21).
-/

variable {G : Type} [Group G] {Lab : Type}

/-- The linear representation of `G` on `ℂ^{dim Q}` given by the unitary matrices `π Q g`. -/
def labelRep (dim : Lab → ℕ) (π : (Q : Lab) → G →* Matrix.unitaryGroup (Fin (dim Q)) ℂ)
    (Q : Lab) : Representation ℂ G (Fin (dim Q) → ℂ) where
  toFun g := Matrix.toLin' (π Q g : Matrix (Fin (dim Q)) (Fin (dim Q)) ℂ)
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' g h := by
    rw [map_mul, Submonoid.coe_mul, Matrix.toLin'_mul, Module.End.mul_eq_comp]

/-- The basis of a space made of multiplets `i : I` with labels `Qi i`: pairs `⟨i, m⟩` with
`m : Fin (dim (Qi i))` the internal quantum number. -/
abbrev Multiplets {I : Type} (dim : Lab → ℕ) (Qi : I → Lab) : Type :=
  Σ i : I, Fin (dim (Qi i))

/-- The symmetry transformation on a multiplet space: the block-diagonal matrix with block
`π (Qi i) g` on multiplet `i`. On the kept block states (`I = K`) this is the paper's `V(g)`, on
the local states of the site (`I = Λ`) it is `L(g)`. -/
def multipletRep {I : Type} [DecidableEq I] (dim : Lab → ℕ)
    (π : (Q : Lab) → G →* Matrix.unitaryGroup (Fin (dim Q)) ℂ) (Qi : I → Lab) (g : G) :
    Matrix (Multiplets dim Qi) (Multiplets dim Qi) ℂ :=
  Matrix.blockDiagonal' fun i => (π (Qi i) g : Matrix (Fin (dim (Qi i))) (Fin (dim (Qi i))) ℂ)

/-- The symmetry transformation `U(g) = V(g) ⊗ L(g)` on the new space
(block states) × (local states), indexed block first. -/
def newRep {K Λ : Type} [DecidableEq K] [DecidableEq Λ] (dim : Lab → ℕ)
    (π : (Q : Lab) → G →* Matrix.unitaryGroup (Fin (dim Q)) ℂ) (Qu : K → Lab) (ql : Λ → Lab)
    (g : G) :
    Matrix (Multiplets dim Qu × Multiplets dim ql) (Multiplets dim Qu × Multiplets dim ql) ℂ :=
  multipletRep dim π Qu g ⊗ₖ multipletRep dim π ql g

/-- The canonical multiplets `ĩ = ((u, µ), Q_ĩ)` of (21): a kept multiplet `u`, a local multiplet
`µ`, and a label `Q_ĩ` occurring in `q_µ ⊗ Q_u` (one copy per label: multiplicity-free coupling). -/
abbrev Can {K Λ : Type} (couple : Lab → Lab → Finset Lab) (Qu : K → Lab) (ql : Λ → Lab) : Type :=
  Σ p : K × Λ, {Q' // Q' ∈ couple (ql p.2) (Qu p.1)}

/-- The label `Q_ĩ` of a canonical multiplet. -/
abbrev canLabel {K Λ : Type} (couple : Lab → Lab → Finset Lab) (Qu : K → Lab) (ql : Λ → Lab)
    (c : Can couple Qu ql) : Lab :=
  c.2.1

/-- The canonical basis (21). Column `⟨ĩ, Q^z_ĩ⟩`, `ĩ = ((u, µ), Q_ĩ)`, is the vector
`|ĩ, Q_ĩ, Q^z_ĩ⟩ = Σ_{Q^z_u, q^z_µ} ⟨q_µ q^z_µ; Q_u Q^z_u | Q_ĩ Q^z_ĩ⟩ |u, Q^z_u; µ, q^z_µ⟩`:
its entry at the block/local basis state `(⟨u', a⟩, ⟨µ', k⟩)` is the Clebsch–Gordan coefficient
`cg (q_µ) (Q_u) (Q_ĩ) ((k, a), Q^z_ĩ)` when `u' = u` and `µ' = µ`, and `0` otherwise. -/
def canonicalBasis {K Λ : Type} [DecidableEq K] [DecidableEq Λ] (dim : Lab → ℕ)
    (couple : Lab → Lab → Finset Lab)
    (cg : (q Q Q' : Lab) → Matrix (Fin (dim q) × Fin (dim Q)) (Fin (dim Q')) ℂ)
    (Qu : K → Lab) (ql : Λ → Lab) :
    Matrix (Multiplets dim Qu × Multiplets dim ql) (Multiplets dim (canLabel couple Qu ql)) ℂ :=
  Matrix.of fun x c =>
    if h : x.1.1 = c.1.1.1 ∧ x.2.1 = c.1.1.2 then
      cg (ql c.1.1.2) (Qu c.1.1.1) c.1.2.1
        (Fin.cast (congrArg (fun l => dim (ql l)) h.2) x.2.2,
          Fin.cast (congrArg (fun u => dim (Qu u)) h.1) x.1.2) c.2
    else 0

/-- The symmetry transformation on the space of iteration `n − 1`, whose multiplets are the
discarded ones `d : D` (labels `Qd d`) followed by the kept ones `u : K` (labels `Qu u`). -/
def prevRep {D K : Type} [DecidableEq D] [DecidableEq K] (dim : Lab → ℕ)
    (π : (Q : Lab) → G →* Matrix.unitaryGroup (Fin (dim Q)) ℂ) (Qd : D → Lab) (Qu : K → Lab)
    (g : G) :
    Matrix (Multiplets dim Qd ⊕ Multiplets dim Qu) (Multiplets dim Qd ⊕ Multiplets dim Qu) ℂ :=
  Matrix.fromBlocks (multipletRep dim π Qd g) 0 0 (multipletRep dim π Qu g)

/-- The operator `R^{[n−1]}` of (39) on the space of iteration `n − 1`: the weighted projection
`Σ_{i ∈ D} w_i Σ_{Q^z} |i, Q_i, Q^z⟩⟨i, Q_i, Q^z|` on the discarded multiplets, plus an operator `T`
on the kept multiplets (in (39), `T = Tr_{site n} R^{[n]}`). -/
def truncatedOperator {D K : Type} [DecidableEq D] (dim : Lab → ℕ) (Qd : D → Lab) (Qu : K → Lab)
    (w : D → ℝ) (T : Matrix (Multiplets dim Qu) (Multiplets dim Qu) ℂ) :
    Matrix (Multiplets dim Qd ⊕ Multiplets dim Qu) (Multiplets dim Qd ⊕ Multiplets dim Qu) ℂ :=
  Matrix.fromBlocks
    (Matrix.blockDiagonal' fun d =>
      (w d : ℂ) • (1 : Matrix (Fin (dim (Qd d))) (Fin (dim (Qd d))) ℂ)) 0 0 T

end NonAbelianDMNRG.Recursion


