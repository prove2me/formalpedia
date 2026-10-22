-- Prove2me | Definitions.Def_PTCommutant_OperatorBasis_Model
-- name    : PTCommutant_OperatorBasis_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T09:28:44.914913+00:00
-- url     : https://prove2.me/theorems/468c54b5-da4a-4b25-880c-f43aa5486415
-- title:
--   eqs. (1), (7), (15), (16), Defs. 2, 4, 5, 24, fn. 4, pp. 2–6, 15 — partial transpose ′ on the last site, f_ab, ψ^k_i(α,r), v^{ab}_{ij}(α), E^α_{ij}, the algebra A
-- statement:
--   This file fixes the objects of the analysis of the algebra $\mathcal A$ of partially transposed permutation operators on $n$ copies of $\mathbb C^d$ (Studziński, Horodecki, Mozrzymas, §III).
--
--   **Space and permutation operators.** Write $\mathcal H=\mathbb C^d$. Operators on $\mathcal H^{\otimes k}$ are matrices indexed by strings $x=(x_1,\dots,x_k)\in\{1,\dots,d\}^k$. For $\sigma\in S(k)$ the permutation operator $V(\sigma)$ of eq. (1) acts as $V(\sigma)|i_1\dots i_k\rangle=|i_{\sigma^{-1}(1)}\dots i_{\sigma^{-1}(k)}\rangle$; it is the published operator `tensorPermutation`.
--
--   **Partial transposition.** For an operator $X$ on $\mathcal H^{\otimes k}$, $X'$ denotes the transpose on the **last** system only:
--   $$\big(|x_1\dots x_{k-1}x_k\rangle\langle y_1\dots y_{k-1}y_k|\big)'=|x_1\dots x_{k-1}y_k\rangle\langle y_1\dots y_{k-1}x_k|.$$
--   The algebra $\mathcal A$ is the complex linear span of the operators $V'(\tau)$, $\tau\in S(n)$.
--
--   **Embeddings and the maps $f_{ab}$.** $S(k)$ sits inside $S(k+j)$ as the permutations fixing the last $j$ systems. Fix $\pi_1,\dots,\pi_{n-1}\in S(n-1)$ and write $(n\ n-1)$ for the transposition of the last two systems. For $a,b\in\{1,\dots,n-1\}$ the map $f_{ab}:S(n-2)\to S(n)$ of eq. (7) is
--   $$f_{ab}(\sigma)=\pi_b\circ\sigma\circ(n\ n-1)\circ\pi_a^{-1}.$$
--
--   **Irreps and the Schur basis (standing data).** An *irrep family* is a finite list of matrix representations $\varphi^\alpha$ of $S(n-2)$ of dimensions $d_\alpha\ge1$ whose matrices are real orthogonal, which are irreducible over $\mathbb C$, and which are pairwise inequivalent over $\mathbb C$ (every intertwiner between two different labels is zero). A *Schur basis* adapted to it is a family of vectors $|\phi_i(\alpha,r)\rangle\in\mathcal H^{\otimes(n-2)}$, with $\alpha$ a label, $r$ in a finite multiplicity set (possibly empty) and $1\le i\le d_\alpha$, that is orthonormal, spans $\mathcal H^{\otimes(n-2)}$, and satisfies
--   $$V(\sigma)|\phi_j(\alpha,r)\rangle=\sum_i\varphi^\alpha_{ij}(\sigma)\,|\phi_i(\alpha,r)\rangle\qquad(\sigma\in S(n-2)).$$
--
--   **The vectors and operators of §III.C.** With $|\Phi^+\rangle=\frac1{\sqrt d}\sum_{l=1}^d|ll\rangle$ on systems $n-1,n$ (Remark 3),
--   $$|\psi^k_i(\alpha,r)\rangle=\sqrt d\,V(\pi_k)\,|\phi_i(\alpha,r)\rangle|\Phi^+\rangle\quad\text{(Definition 4)},\qquad v^{ab}_{ij}(\alpha)=\sum_r|\psi^a_i(\alpha,r)\rangle\langle\psi^b_j(\alpha,r)|\quad\text{(Definition 5)},$$
--   and $E^\alpha_{ij}=\sum_r|\phi_i(\alpha,r)\rangle\langle\phi_j(\alpha,r)|$ on $\mathcal H^{\otimes(n-2)}$ (footnote 4). Finally $X\otimes\mathbb 1_{n-1,n}$ extends an operator on the first $n-2$ systems by the identity on the last two.
--
--   These definitions are the common vocabulary of every statement in the mission: Theorem 9 expresses $v^{ab}_{ij}(\alpha)$ through the $V'(f_{ba}(\sigma))$ and conversely.
--
--   **Formalization Note.** The paper's $n$ is $m+2$, so $S(n-2)$, $S(n-1)$, $S(n)$ are `Equiv.Perm (Fin m)`, `Equiv.Perm (Fin (m+1))`, `Equiv.Perm (Fin (m+2))`. Systems are 0-based: system $s$ of the paper is index $s-1$, so systems $n-1$ and $n$ are the indices $m$ and $m+1$, and a label $a\in\{1,\dots,n-1\}$ is `a : Fin (m+1)` (index $a-1$). `ptLast` is $'$, `liftPerm k j` the embedding $S(k)\hookrightarrow S(k+j)$, `swapLast m` is $(n\ n-1)$, `fPerm π a b σ` is $f_{ab}(\sigma)$, `IrrepFamily` and `SchurBasis` the standing data, `psi`, `vOp`, `EOp`, `embedOp`, `algA` the remaining objects. Products of permutations compose right to left. The irreps are real-valued (`ℝ`) and cast to $\mathbb C$ where they multiply operators. The factor $\sqrt d$ of Definition 4 and $1/\sqrt d$ of $|\Phi^+\rangle$ are kept literally. `SchurBasis` contains no orthogonality relation of the irreps and no formula of eq. (86); those are theorems of the mission.
-- source:
--   Studziński, Horodecki, Mozrzymas, Commutant structuture of U⊗(n−1)⊗U* transformations, arXiv:1305.6183v2, pp. 1–6 and 15: §I p. 1 (algebra A), eq. (1) p. 2, eqs. (3)–(5) p. 3, eq. (7) p. 4, §III.B p. 4 (partial transposition ′ on the last subsystem), Definition 2 and Remark 3 p. 5, Definitions 4–5 (eqs. (15)–(16)) p. 5, footnote 4 p. 6, real symmetric irreps p. 7, Definition 24 p. 15, Notation 32 p. 24

import Mathlib
import Definitions.Def_QAlgorithms_Defs_TensorPermutationRepresentations

namespace PTCommutant.OperatorBasis
open QAlgorithms.Schur

/-- Computational basis labels of `(ℂ^d)^{⊗k}`: a string `x : Fin k → Fin d`.
System number `s + 1` of the paper is the index `s : Fin k` (0-based). -/
abbrev Site (d k : ℕ) := Fin k → Fin d

/-- Operators on `(ℂ^d)^{⊗k}` as matrices in the computational basis. -/
abbrev Op (d k : ℕ) := Matrix (Site d k) (Site d k) ℂ

/-- `′`: partial transposition on the last system only (§III.B, p. 4).
On matrix units, `|x⟩⟨y| ↦ |x[last ↦ y_last]⟩⟨y[last ↦ x_last]|`; entrywise
`X′ x y = X (x with last entry y_last) (y with last entry x_last)`. -/
def ptLast {d k : ℕ} (X : Op d (k + 1)) : Op d (k + 1) :=
  Matrix.of fun x y =>
    X (Function.update x (Fin.last k) (y (Fin.last k)))
      (Function.update y (Fin.last k) (x (Fin.last k)))

/-- The embedding `S(k) ↪ S(k + j)`: a permutation of the first `k` systems, fixing the
trailing `j` systems. It is a group homomorphism. -/
def liftPerm (k j : ℕ) : Equiv.Perm (Fin k) →* Equiv.Perm (Fin (k + j)) :=
  Equiv.Perm.extendDomainHom (Fin.castLEquiv (Nat.le_add_right k j))

/-- The transposition `(n n−1)` of the last two systems of `n = m + 2` systems
(Lean indices `m` and `m + 1`). -/
def swapLast (m : ℕ) : Equiv.Perm (Fin (m + 2)) :=
  Equiv.swap ⟨m, by omega⟩ (Fin.last (m + 1))

/-- The map `f_ab : S(n−2) → S(n)`, `f_ab(σ) = π_b ∘ σ ∘ (n n−1) ∘ π_a⁻¹` (eq. (7)), with
`n = m + 2`, `π_k ∈ S(n−1)` and `σ ∈ S(n−2)` embedded into `S(n)` by `liftPerm`.
The labels `a b : Fin (m+1)` are the paper's `1, …, n−1` shifted to `0, …, m`. -/
def fPerm {m : ℕ} (π : Fin (m + 1) → Equiv.Perm (Fin (m + 1))) (a b : Fin (m + 1))
    (σ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 2)) :=
  liftPerm (m + 1) 1 (π b) * liftPerm m 2 σ * swapLast m * (liftPerm (m + 1) 1 (π a))⁻¹

/-- A family of irreducible matrix representations `φ^α` of `S(n−2) = S(m)` with real
orthogonal matrices (p. 7: "symmetric and real matrices"), irreducible over `ℂ` and pairwise
inequivalent over `ℂ` (Notation 32, p. 24). `dim α` is the paper's `d_α`. -/
structure IrrepFamily (m : ℕ) where
  /-- the labels `α` of the irreps -/
  ι : Type
  [instFintype : Fintype ι]
  [instDecEq : DecidableEq ι]
  /-- `d_α = dim φ^α` -/
  dim : ι → ℕ
  /-- the matrix representation `σ ↦ φ^α(σ)` -/
  rep : (α : ι) → Equiv.Perm (Fin m) →* Matrix (Fin (dim α)) (Fin (dim α)) ℝ
  /-- real orthogonal matrices -/
  orth : ∀ α σ, rep α σ ∈ Matrix.orthogonalGroup (Fin (dim α)) ℝ
  dim_pos : ∀ α, 0 < dim α
  /-- irreducible over `ℂ`: the only invariant subspaces of `ℂ^{d_α}` are `0` and everything -/
  irred : ∀ α (W : Submodule ℂ (Fin (dim α) → ℂ)),
    (∀ σ, ∀ w ∈ W, ((rep α σ).map Complex.ofReal).mulVec w ∈ W) → W = ⊥ ∨ W = ⊤
  /-- pairwise inequivalent: every intertwiner between distinct labels vanishes -/
  inequiv : ∀ α β, α ≠ β → ∀ T : Matrix (Fin (dim β)) (Fin (dim α)) ℂ,
    (∀ σ, T * (rep α σ).map Complex.ofReal = (rep β σ).map Complex.ofReal * T) → T = 0

attribute [instance] IrrepFamily.instFintype IrrepFamily.instDecEq

/-- A Schur basis `|φ_i(α,r)⟩` of `(ℂ^d)^{⊗(n−2)} = (ℂ^d)^{⊗m}` adapted to the family `F`
(eqs. (3)–(5), footnote 4): orthonormal, complete, and transforming by
`V(σ)|φ_j(α,r)⟩ = Σ_i φ^α_{ij}(σ) |φ_i(α,r)⟩`. `R α` indexes the multiplicity `r` of `α`
(possibly empty). -/
structure SchurBasis {m : ℕ} (F : IrrepFamily m) (d : ℕ) where
  /-- the multiplicity labels `r` of each irrep -/
  R : F.ι → Type
  [instFintype : ∀ α, Fintype (R α)]
  [instDecEq : ∀ α, DecidableEq (R α)]
  /-- the basis vector `|φ_i(α,r)⟩` -/
  vec : (α : F.ι) → R α → Fin (F.dim α) → (Site d m → ℂ)
  orth_same : ∀ α r i s j,
    star (vec α r i) ⬝ᵥ vec α s j = if r = s ∧ i = j then 1 else 0
  orth_diff : ∀ α β, α ≠ β → ∀ r i s j, star (vec α r i) ⬝ᵥ vec β s j = 0
  complete : Submodule.span ℂ
    (Set.range fun t : (Σ α, R α × Fin (F.dim α)) => vec t.1 t.2.1 t.2.2) = ⊤
  equivariant : ∀ α r j (σ : Equiv.Perm (Fin m)),
    (tensorPermutation d m σ).mulVec (vec α r j) =
      ∑ i, ((F.rep α σ i j : ℝ) : ℂ) • vec α r i

attribute [instance] SchurBasis.instFintype SchurBasis.instDecEq

/-- `|φ⟩|Φ+⟩`, with `|Φ+⟩ = (1/√d) Σ_l |l l⟩` on systems `n−1, n` (Remark 3, p. 5). -/
noncomputable def withPhiPlus {d m : ℕ} (φ : Site d m → ℂ) : Site d (m + 2) → ℂ :=
  fun x => φ (fun i => x (Fin.castLE (by omega) i)) *
    (if x ⟨m, by omega⟩ = x (Fin.last (m + 1)) then ((Real.sqrt d : ℝ) : ℂ)⁻¹ else 0)

/-- `|ψ^k_i(α,r)⟩ = √d V(π_k)|φ_i(α,r)⟩|Φ+⟩` (Definition 4, eq. (15)). -/
noncomputable def psi {m d : ℕ} {F : IrrepFamily m} (B : SchurBasis F d)
    (π : Fin (m + 1) → Equiv.Perm (Fin (m + 1))) (k : Fin (m + 1)) (α : F.ι) (r : B.R α)
    (i : Fin (F.dim α)) : Site d (m + 2) → ℂ :=
  ((Real.sqrt d : ℝ) : ℂ) •
    (tensorPermutation d (m + 2) (liftPerm (m + 1) 1 (π k))).mulVec (withPhiPlus (B.vec α r i))

/-- `v^{ab}_{ij}(α) = Σ_r |ψ^a_i(α,r)⟩⟨ψ^b_j(α,r)|` (Definition 5, eq. (16)). -/
noncomputable def vOp {m d : ℕ} {F : IrrepFamily m} (B : SchurBasis F d)
    (π : Fin (m + 1) → Equiv.Perm (Fin (m + 1))) (a b : Fin (m + 1)) (α : F.ι)
    (i j : Fin (F.dim α)) : Op d (m + 2) :=
  ∑ r, Matrix.vecMulVec (psi B π a α r i) (star (psi B π b α r j))

/-- `E^α_{ij} = Σ_r |φ_i(α,r)⟩⟨φ_j(α,r)|` (footnote 4, p. 6). -/
noncomputable def EOp {m d : ℕ} {F : IrrepFamily m} (B : SchurBasis F d) (α : F.ι)
    (i j : Fin (F.dim α)) : Op d m :=
  ∑ r, Matrix.vecMulVec (B.vec α r i) (star (B.vec α r j))

/-- `X ⊗ 1_{n−1,n}`: an operator on the first `n−2` systems extended by the identity on the
last two. -/
def embedOp {d m : ℕ} (X : Op d m) : Op d (m + 2) :=
  Matrix.of fun x y =>
    X (fun i => x (Fin.castLE (by omega) i)) (fun i => y (Fin.castLE (by omega) i)) *
      (if x ⟨m, by omega⟩ = y ⟨m, by omega⟩ ∧ x (Fin.last (m + 1)) = y (Fin.last (m + 1))
        then 1 else 0)

/-- The represented group algebra `ℂ[S(n−2)]`: the span of permutation operators on the
first `m = n−2` systems. -/
noncomputable def groupAlg (d m : ℕ) : Submodule ℂ (Op d m) :=
  Submodule.span ℂ
    (Set.range fun σ : Equiv.Perm (Fin m) => tensorPermutation d m σ)

/-- The ideal `M` generated by the partially transposed permutations `V′(σ_ab)` with
`σ_ab(n) ≠ n` (§III.B–C, pp. 4–6). -/
noncomputable def algM (d m : ℕ) : Submodule ℂ (Op d (m + 2)) :=
  Submodule.span ℂ
    (Set.range fun τ : {τ : Equiv.Perm (Fin (m + 2)) //
        τ (Fin.last (m + 1)) ≠ Fin.last (m + 1)} =>
      ptLast (tensorPermutation d (m + 2) τ.1))

/-- The algebra `A` of partially transposed permutation operators on `n = m + 2` systems
(§I, p. 1): the span of `V′(τ)`, `τ ∈ S(n)`. -/
noncomputable def algA (d m : ℕ) : Submodule ℂ (Op d (m + 2)) :=
  Submodule.span ℂ
    (Set.range fun τ : Equiv.Perm (Fin (m + 2)) => ptLast (tensorPermutation d (m + 2) τ))

end PTCommutant.OperatorBasis


