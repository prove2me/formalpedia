-- Prove2me | Definitions.Def_QCollLB_Harmonic
-- name    : QCollLB_Harmonic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:12:45.17759+00:00
-- url     : https://prove2.me/theorems/6715bfc1-0e62-4d02-930a-a82a6f42e715
-- title:
--   §§4–5.2, §7.1 — partial-injection databases, isotypic and harmonic spaces, the completion map $A$, the frame normalization $\Gamma_n$ and the encoding $V$
-- statement:
--   Let $P=\mathbb C[S_n]$ and let $\mathcal I_n$ be the set of partial injections $d:[n]\rightharpoonup[n]$, with database space $D=\mathbb C[\mathcal I_n]$ and size components $D_s=\mathrm{span}\{|d\rangle:|d|=s\}$, $D_{\le t}=\bigoplus_{s\le t}D_s$.
--
--   **Actions and isotypic subspaces.** $S_n$ acts on $P$ by left multiplication $L_\tau|\pi\rangle=|\tau\circ\pi\rangle$, and on $D$ by range relabelling $|d\rangle\mapsto|\tau\circ d\rangle$ and domain relabelling $|d\rangle\mapsto|d\circ\sigma^{-1}\rangle$. For a partition $\lambda\vdash n$ the $\lambda$-isotypic subspace of a representation is the sum of all its irreducible subrepresentations of type $\lambda$. $P_\lambda$ is the left-regular $\lambda$-isotypic subspace, and for $0\le s\le n-1$
--   $$
--   P_s=\bigoplus_{\lambda_1=n-s}P_\lambda,\qquad P_{\le t}=\bigoplus_{s\le t}P_s .
--   $$
--   $D^{(s)}_R$ (resp. $D^{(s)}_D$) is the sum of the $\lambda$-isotypic subspaces of the range (resp. domain) action on $D_s$ over $\lambda_1=n-s$; $K^{(s)}_R,K^{(s)}_D$ are their projectors and $K_R=\bigoplus_sK^{(s)}_R$, $K_D=\bigoplus_sK^{(s)}_D$.
--
--   **Encoding.** $A_s|d\rangle=|v_d\rangle=((n-s)!)^{-1/2}\sum_{\pi\supseteq d}|\pi\rangle$ and $A=\sum_sA_sP_{D_s}$. For $\lambda=(n-s,\nu)$, $\gamma_{n,\lambda}=\binom ns f^\nu/f^\lambda>0$, $\Gamma_n=\sum_\lambda\gamma_{n,\lambda}P_{P_\lambda}$, and
--   $$
--   V_s=A_s^\dagger\Gamma_n^{-1/2}\big|_{P_s},\qquad V=\sum_{s=0}^{n-1}V_sP_{P_s}:P\to D .
--   $$
--
--   **Auxiliary notation.** A function $h:S_n\to\mathbb C$ is identified with $n!^{-1/2}\sum_\pi h(\pi)|\pi\rangle\in P$ (its norm is the uniform-measure norm). $P_B$ is the diagonal projector on $D$ asserting $B\subseteq\mathrm{Im}\,d$. For tuples $u,v$ the iterated difference is $(I-L_{(u_kv_k)})\cdots(I-L_{(u_1v_1)})$, and $T_j=\{u_j,\dots,u_k\}$.
--
--   **Formalization Note** Partial injections, $D_s$, $A_sP_{D_s}$, $P_\lambda$, $\lambda_1$ and $\gamma_{n,\lambda}$ are the published `CompPermOracle.PartialPerm`, `Lsub`, `synth`, `block`, `firstRow` and `gramEig`. The irreducible of type $\lambda$ is the published Specht module `SpechtActual.rep λ`, and isotypic components are Mathlib's `isotypicComponent` over $\mathbb C[S_n]$. $\gamma_{n,\lambda}$ is computed by the product formula $\prod_{j\le\nu_1}(1+\nu'_j/(n-s-j+1))$ printed in Eq. (44), which the paper proves equal to $\binom ns f^\nu/f^\lambda$. $\Gamma_n^{\pm1/2}$ are written on the eigendecomposition $\sum_\lambda\gamma_{n,\lambda}^{\pm1/2}P_{P_\lambda}$. $D^R_{s,\lambda}$ is the isotypic subspace of $D$ intersected with the invariant subspace $D_s$, and operators defined on $D_s$ are extended by zero. Ancillary registers are written first (`ampSub`).
-- source:
--   Peng–Wu, Quantum Lower Bounds for Collision Problems, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), §4.1 p.20, Definitions 5.1 p.22, 5.4 p.24, 5.6 p.25, 5.12 p.30, 5.13 p.31, §7.1 p.52

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_Levels
import Definitions.Def_CompPermOracle_spechtBlock

namespace QCollLB

open CompPermOracle OAI.PartialPermutation OAI.PartialPermutation.DiagramCounting

/-- The unitary representation of a group `G` on `ℂ[X]` induced by an action `act` of `G` on the
finite set `X` by permutations: `g · |x⟩ = |act(g) x⟩`, i.e. `(g · v)(x) = v(act(g)⁻¹ x)`
(Peng–Wu, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), §4.1, p.20). -/
noncomputable def permRep {G X : Type*} [Group G] [Fintype X] (act : G →* Equiv.Perm X) :
    Representation ℂ G (Hil X) where
  toFun g :=
    { toFun := fun v => WithLp.toLp 2 fun x => v ((act g).symm x)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by
    ext v x
    simp only [map_one]
    rfl
  map_mul' := by
    intro g h
    ext v x
    simp only [map_mul]
    rfl

/-- The range relabelling `d ↦ τ ∘ d` of partial injections by `τ ∈ S_n` (arXiv:2611.01767,
§4.1, p.20: "the first factor relabels the range"; §5.2, p.25: `χ_R^{(s)}(τ)|d⟩ = |τ ∘ d⟩`). -/
def rangeAct (n : ℕ) : Equiv.Perm (Fin n) →* Equiv.Perm (PartialPerm n) where
  toFun τ :=
    { toFun := fun d => d.trans τ.toPEquiv
      invFun := fun d => d.trans τ.symm.toPEquiv
      left_inv := fun d => by
        simp [PEquiv.trans_assoc, ← Equiv.toPEquiv_trans, PEquiv.trans_refl]
      right_inv := fun d => by
        simp [PEquiv.trans_assoc, ← Equiv.toPEquiv_trans, PEquiv.trans_refl] }
  map_one' := by
    ext d : 1
    show d.trans (Equiv.refl _).toPEquiv = d
    simp [PEquiv.trans_refl]
  map_mul' := by
    intro σ τ
    ext d : 1
    simp [Equiv.Perm.mul_def, Equiv.toPEquiv_trans, PEquiv.trans_assoc]

/-- The domain relabelling `d ↦ d ∘ σ⁻¹` of partial injections by `σ ∈ S_n` (arXiv:2611.01767,
§4.1, p.20: "the second relabels the domain"; §5.2, p.25: `χ_D^{(s)}(σ)|d⟩ = |d ∘ σ⁻¹⟩`). -/
def domainAct (n : ℕ) : Equiv.Perm (Fin n) →* Equiv.Perm (PartialPerm n) where
  toFun σ :=
    { toFun := fun d => σ.symm.toPEquiv.trans d
      invFun := fun d => σ.toPEquiv.trans d
      left_inv := fun d => by
        simp [← PEquiv.trans_assoc, ← Equiv.toPEquiv_trans, PEquiv.refl_trans]
      right_inv := fun d => by
        simp [← PEquiv.trans_assoc, ← Equiv.toPEquiv_trans, PEquiv.refl_trans] }
  map_one' := by
    ext d : 1
    show (Equiv.refl _).symm.toPEquiv.trans d = d
    simp [PEquiv.refl_trans]
  map_mul' := by
    intro σ τ
    ext d : 1
    simp [Equiv.Perm.mul_def, Equiv.toPEquiv_trans, PEquiv.trans_assoc]

/-- The range representation `χ_R` of `S_n` on the database space `D = ℂ[I_n]`
(arXiv:2611.01767, §5.2, p.25). -/
noncomputable def rangeRep (n : ℕ) : Representation ℂ (Equiv.Perm (Fin n)) (Hil (PartialPerm n)) :=
  permRep (rangeAct n)

/-- The domain representation `χ_D` of `S_n` on the database space `D = ℂ[I_n]`
(arXiv:2611.01767, §5.2, p.25). -/
noncomputable def domainRep (n : ℕ) : Representation ℂ (Equiv.Perm (Fin n)) (Hil (PartialPerm n)) :=
  permRep (domainAct n)

/-- The range relabelling operator `L_τ|d⟩ = |τ ∘ d⟩` on `D` (arXiv:2611.01767, §7.1, p.52). -/
noncomputable def rangeOp (n : ℕ) (τ : Equiv.Perm (Fin n)) :
    Hil (PartialPerm n) →L[ℂ] Hil (PartialPerm n) :=
  LinearMap.toContinuousLinearMap (rangeRep n τ)

/-- The left-regular operator `L_τ|π⟩ = |τ ∘ π⟩` on `P = ℂ[S_n]` (arXiv:2611.01767, §4.1, p.20:
`L_a|g⟩ = |ag⟩`; §7.1, p.52). It is the published `regularRep`. -/
noncomputable def leftOp (n : ℕ) (τ : Equiv.Perm (Fin n)) :
    Hil (Equiv.Perm (Fin n)) →L[ℂ] Hil (Equiv.Perm (Fin n)) :=
  LinearMap.toContinuousLinearMap (regularRep (Equiv.Perm (Fin n)) τ)

/-- The `λ`-isotypic subspace of a representation `ρ` of `S_n`: the sum of all irreducible
subrepresentations of type `λ` (arXiv:2611.01767, §4.1, p.20: "The `λ`-isotypic subspace is the
sum of all irreducible copies of type `λ`").

**Formalization Note.** The irreducible of type `λ ⊢ n` is the published Specht module
`SpechtActual.rep λ` (row tabloids and polytabloids, so `λ = (n)` is the trivial representation).
The isotypic component is Mathlib's `isotypicComponent` over the group algebra `ℂ[S_n]` (the sum of
all submodules isomorphic to that simple module), viewed as a complex subspace. -/
noncomputable def isotypicSub {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) (lam : Shape n) : Submodule ℂ V :=
  (isotypicComponent (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) ρ.asModule
    (Representation.asModule (SpechtActual.rep lam))).restrictScalars ℂ

/-- `P_s = ⨁_{λ ⊢ n, λ_1 = n − s} P_λ` for `0 ≤ s ≤ n − 1`, and `P_s = {0}` outside this range
(arXiv:2611.01767, Definition 5.4, p.24), with `P_λ` the left-regular `λ`-isotypic subspace of
`P = ℂ[S_n]` (§4.1, p.20).

**Formalization Note.** `P_λ` is the published `CompPermOracle.block λ` (the `λ`-isotypic component
of the left regular representation `|π⟩ ↦ |τπ⟩`) and `λ_1` is `CompPermOracle.firstRow λ`.
`λ_1 = n − s` is written `λ_1 + s = n`, with no natural-number subtraction. -/
noncomputable def PsSub (n s : ℕ) : Submodule ℂ (Hil (Equiv.Perm (Fin n))) :=
  if s < n then ⨆ (lam : Shape n) (_ : firstRow lam + s = n), block lam else ⊥

/-- `P_{≤t} = ⨁_{s ≤ t} P_s`, the vectors of permutation degree at most `t` (arXiv:2611.01767,
Definition 5.4, p.24). -/
noncomputable def PLe (n t : ℕ) : Submodule ℂ (Hil (Equiv.Perm (Fin n))) :=
  ⨆ (s : ℕ) (_ : s ≤ t), PsSub n s

/-- `D_{≤t} = ⨁_{s ≤ t} D_s`, the database vectors supported on partial injections with at most
`t` assignments (arXiv:2611.01767, Definition 5.1, Eq. (28), p.22). `D_s` is the published
`CompPermOracle.Lsub n s = span{|d⟩ : |d| = s}`. -/
noncomputable def DLe (n t : ℕ) : Submodule ℂ (Hil (PartialPerm n)) :=
  ⨆ (s : ℕ) (_ : s ≤ t), Lsub n s

/-- `D^R_{s,λ}`, the `λ`-isotypic subspace of the range action on `D_s` (arXiv:2611.01767, §5.2,
p.25).

**Formalization Note.** The range representation is defined on all of `D`; `D_s` is invariant, so the
`λ`-isotypic subspace of `D_s` is the `λ`-isotypic subspace of `D` intersected with `D_s`. -/
noncomputable def DRsl (n s : ℕ) (lam : Shape n) : Submodule ℂ (Hil (PartialPerm n)) :=
  isotypicSub (rangeRep n) lam ⊓ Lsub n s

/-- `D^D_{s,λ}`, the `λ`-isotypic subspace of the domain action on `D_s` (arXiv:2611.01767, §5.2,
p.25). Same convention as `DRsl`. -/
noncomputable def DDsl (n s : ℕ) (lam : Shape n) : Submodule ℂ (Hil (PartialPerm n)) :=
  isotypicSub (domainRep n) lam ⊓ Lsub n s

/-- The range-harmonic space `D^{(s)}_R = ⨁_{λ ⊢ n, λ_1 = n − s} D^R_{s,λ}` (arXiv:2611.01767,
Definition 5.6, Eq. (35), p.25). `λ_1 = n − s` is written `λ_1 + s = n`. -/
noncomputable def DRs (n s : ℕ) : Submodule ℂ (Hil (PartialPerm n)) :=
  ⨆ (lam : Shape n) (_ : firstRow lam + s = n), DRsl n s lam

/-- The domain-harmonic space `D^{(s)}_D = ⨁_{λ ⊢ n, λ_1 = n − s} D^D_{s,λ}` (arXiv:2611.01767,
Definition 5.6, Eq. (35), p.25). -/
noncomputable def DDs (n s : ℕ) : Submodule ℂ (Hil (PartialPerm n)) :=
  ⨆ (lam : Shape n) (_ : firstRow lam + s = n), DDsl n s lam

/-- `K^{(s)}_R`, the orthogonal projector onto `D^{(s)}_R` (arXiv:2611.01767, Eq. (35), p.25).

**Formalization Note.** The paper's `K^{(s)}_R : D_s → D_s` is extended by `0` on the other size
components (it is the orthogonal projector of `D` onto `D^{(s)}_R ⊆ D_s`). -/
noncomputable def KRs (n s : ℕ) : Hil (PartialPerm n) →L[ℂ] Hil (PartialPerm n) :=
  (DRs n s).starProjection

/-- `K^{(s)}_D`, the orthogonal projector onto `D^{(s)}_D` (arXiv:2611.01767, Eq. (35), p.25),
extended by `0` as for `KRs`. -/
noncomputable def KDs (n s : ℕ) : Hil (PartialPerm n) →L[ℂ] Hil (PartialPerm n) :=
  (DDs n s).starProjection

/-- `K_R = ⨁_{s=0}^n K^{(s)}_R` (arXiv:2611.01767, Eq. (35), p.25). -/
noncomputable def KR (n : ℕ) : Hil (PartialPerm n) →L[ℂ] Hil (PartialPerm n) :=
  ∑ s ∈ Finset.range (n + 1), KRs n s

/-- `K_D = ⨁_{s=0}^n K^{(s)}_D` (arXiv:2611.01767, Eq. (35), p.25). -/
noncomputable def KD (n : ℕ) : Hil (PartialPerm n) →L[ℂ] Hil (PartialPerm n) :=
  ∑ s ∈ Finset.range (n + 1), KDs n s

/-- The full synthesis map `A = Σ_{s=0}^n A_s P_{D_s}` (arXiv:2611.01767, Definition 5.12,
Eq. (41), p.30), where `A_s|d⟩ = |v_d⟩ = ((n−s)!)^{−1/2} Σ_{π ⊇ d} |π⟩`.

**Formalization Note.** `A_s P_{D_s}` is the published `CompPermOracle.synth n s`
(`Σ_{|d| = s} |v_d⟩⟨d|`, with `|v_d⟩ = CompPermOracle.completion d`). -/
noncomputable def Asyn (n : ℕ) : Hil (PartialPerm n) →L[ℂ] Hil (Equiv.Perm (Fin n)) :=
  ∑ s ∈ Finset.range (n + 1), synth n s

/-- The frame normalization `Γ_n = Σ_{λ ⊢ n} γ_{n,λ} P_{P_λ}` (arXiv:2611.01767, Definition 5.13,
Eq. (43), p.31).

**Formalization Note.** `γ_{n,λ}` is the published `CompPermOracle.gramEig λ`
`= ∏_{c < λ_1} (1 + (λ'_c − 1)/(λ_1 − c))`. For `λ = (n − s, ν)` this is the product
`∏_{j=1}^{ν_1} (1 + ν'_j/(n − s − j + 1))` of Eq. (44), p.31 (factors with `j > ν_1` equal `1`),
which the paper proves equal to its defining value `C(n,s) f^ν/f^λ` (Lemma 5.14 via the hook-length
formula). -/
noncomputable def Gamma (n : ℕ) : Hil (Equiv.Perm (Fin n)) →L[ℂ] Hil (Equiv.Perm (Fin n)) :=
  ∑ lam : Shape n, ((gramEig lam : ℝ) : ℂ) • (block lam).starProjection

/-- `Γ_n^{1/2} = Σ_λ γ_{n,λ}^{1/2} P_{P_λ}` (arXiv:2611.01767, Eq. (46), p.32), written on the
eigen-decomposition of `Γ_n`. -/
noncomputable def GammaSqrt (n : ℕ) : Hil (Equiv.Perm (Fin n)) →L[ℂ] Hil (Equiv.Perm (Fin n)) :=
  ∑ lam : Shape n, ((Real.sqrt (gramEig lam) : ℝ) : ℂ) • (block lam).starProjection

/-- `Γ_n^{−1/2} = Σ_λ γ_{n,λ}^{−1/2} P_{P_λ}` (arXiv:2611.01767, Eq. (43), p.31: "all `γ_{n,λ}` are
positive, so `Γ_n^{−1/2}` is well defined"), written on the eigen-decomposition of `Γ_n`. -/
noncomputable def GammaInvSqrt (n : ℕ) : Hil (Equiv.Perm (Fin n)) →L[ℂ] Hil (Equiv.Perm (Fin n)) :=
  ∑ lam : Shape n, (((Real.sqrt (gramEig lam))⁻¹ : ℝ) : ℂ) • (block lam).starProjection

/-- The component encoding `V_s = A_s† Γ_n^{−1/2}|_{P_s}`, extended by `0` off `P_s`
(arXiv:2611.01767, Definition 5.13, Eq. (43), p.31). -/
noncomputable def Vs (n s : ℕ) : Hil (Equiv.Perm (Fin n)) →L[ℂ] Hil (PartialPerm n) :=
  (ContinuousLinearMap.adjoint (synth n s)).comp
    ((GammaInvSqrt n).comp (PsSub n s).starProjection)

/-- The encoding `V = Σ_{s=0}^{n−1} V_s P_{P_s} : P → D` (arXiv:2611.01767, Definition 5.13,
Eq. (43), p.31). -/
noncomputable def V (n : ℕ) : Hil (Equiv.Perm (Fin n)) →L[ℂ] Hil (PartialPerm n) :=
  ∑ s ∈ Finset.range n, Vs n s

/-- The vector `n!^{−1/2} Σ_π h(π)|π⟩ ∈ P` identified with a function `h : S_n → ℂ`
(arXiv:2611.01767, proof of Lemma 7.1, p.54). Its Euclidean norm is the norm of `h` with respect to
the uniform measure on `S_n` (Claim 7.3, p.53). -/
noncomputable def funVec {n : ℕ} (h : Equiv.Perm (Fin n) → ℂ) : Hil (Equiv.Perm (Fin n)) :=
  ((Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) • WithLp.toLp 2 h

/-- The image set `Im d` of a partial injection (arXiv:2611.01767, §2.4, p.14). -/
def imSet {n : ℕ} (d : PartialPerm n) : Finset (Fin n) :=
  Finset.univ.filter fun y => ¬ NotInIm d y

/-- `P_B`, the diagonal projector on `D` asserting `B ⊆ Im d` (arXiv:2611.01767, §7.1, p.52). -/
noncomputable def PB {n : ℕ} (B : Finset (Fin n)) : Hil (PartialPerm n) →L[ℂ] Hil (PartialPerm n) :=
  ∑ d ∈ Finset.univ.filter (fun d : PartialPerm n => B ⊆ imSet d), ketBra (ket d) (ket d)

/-- `T_j = {u_j, …, u_k}` for a tuple `u_1, …, u_k` (arXiv:2611.01767, Claims 7.2, 7.3, pp.52–53),
0-based: `T_j = {u_{j'} : j' ≥ j}`. -/
def Tset {n k : ℕ} (u : Fin k → Fin n) (j : Fin k) : Finset (Fin n) :=
  (Finset.univ.filter fun j' => j ≤ j').image u

/-- The iterated difference `(I − L_{(u_k v_k)}) ⋯ (I − L_{(u_1 v_1)})`, the factor with `j = 1`
applied first (arXiv:2611.01767, Claims 7.2, 7.3, pp.52–53), for a family `L` of operators indexed
by permutations; `(u v)` is the transposition `Equiv.swap u v`. -/
noncomputable def iterDiff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {n k : ℕ}
    (L : Equiv.Perm (Fin n) → E →L[ℂ] E) (u v : Fin k → Fin n) : E →L[ℂ] E :=
  (List.finRange k).foldl (fun acc j => (1 - L (Equiv.swap (u j) (v j))).comp acc) 1

/-- The amplified subspace `S ⊗ ℂ[Λ] ⊆ ℂ[Λ × X]` of vectors whose every `Λ`-slice lies in `S`
(arXiv:2611.01767, §2.2, p.13: "an operator on one register is extended by the identity on the
others"; e.g. `P_{≤t} ⊗ A`, `D_{≤t} ⊗ A`). The ancillary register comes first. -/
noncomputable def ampSub {Λ X : Type*} [Fintype Λ] [Fintype X] (S : Submodule ℂ (Hil X)) :
    Submodule ℂ (Hil (Λ × X)) :=
  Submodule.span ℂ {v | ∃ u : Hil Λ, ∃ w ∈ S, v = ketTensor u w}

end QCollLB


