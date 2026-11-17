-- Prove2me | Definitions.Def_SingleInteraction_Supplement_Compiler
-- name    : SingleInteraction_Supplement_Compiler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:04:45.837967+00:00
-- url     : https://prove2.me/theorems/6e401458-63f2-4261-b8a2-44eaaff1a469
-- title:
--   The unpinned single-interaction compiler of eq. (28)
-- statement:
--   For $k$-qubit interactions $h^{(1)},\dots,h^{(m)}$ with distinct binary tags $x^{(j)}$ of length $\ell=\lceil\log_2m\rceil$ and a penalty $\Delta$, eq. (28) defines the $(k+\ell+2)$-qubit interaction
--   $$\tilde h_{\mathrm{unp}}=\frac1{\ell+1}\sum_{j=1}^m h^{(j)}_{v_1\ldots v_k}\otimes\Pi^{x^{(j)}_1}_{u_1}\otimes\cdots\otimes\Pi^{x^{(j)}_\ell}_{u_\ell}\otimes I_{u_{\ell+1}u_{\ell+2}}+\Delta\,I\otimes h_{\mathrm{check}}(u_{\ell+1},u_{\ell+2}).$$
--   For a target $K=\sum_{i=1}^Mh^{(j_i)}_{V_i}$ on a working register $W$, each occurrence $i$ receives a block of $\ell+1$ auxiliary pairs and
--   $$\tilde K=\sum_{i=1}^M\sum_{r=1}^{\ell+1}\tilde h_{\mathrm{unp}}(V_i,U_i^{(r)}),$$
--   where in the $r$-th application the $r$-th pair occupies the check positions and the other $\ell$ pairs supply the tag of $h^{(j_i)}$: a selector position with tag bit $0$ receives the first qubit of its pair, with tag bit $1$ the second. The valid auxiliary configuration is $z_{\mathrm{val}}=(01)^{M(\ell+1)}$, $V|\psi\rangle=|\psi\rangle\otimes|z_{\mathrm{val}}\rangle$, and $\tilde K(z)=(I_W\otimes\langle z|)\tilde K(I_W\otimes|z\rangle)$. Also $J=\max_j\|h^{(j)}\|$ and, for a pinned auxiliary state $|\Psi\rangle$ on $p$ qubits, $V|\psi\rangle=|\psi\rangle_W\otimes|\Psi\rangle_A$ (§4.1.3).
--
--   These are the constructions of Theorems 48 and 49.
--
--   **Formalization Note** The register is the working qubits followed by auxiliary qubits indexed by (block, pair, position in the pair). In application $r$ the selector positions use the pairs other than $r$, in order.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §4.1.3, pp.37–38; §4.2.1–4.2.2, eq. (28), pp.39–40

import Mathlib
import Definitions.Def_SingleInteraction_onTuple
import Definitions.Def_SYKEdge_MatrixNorms
import Definitions.Def_SingleInteraction_Supplement_Linalg

namespace SingleInteraction

namespace Supplement

/-!
# The unpinned single-interaction compiler (eq. (28), §4.2)

Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version,
sha256 19ddc444…), §4.2.1–4.2.2, pp.39–40. For a finite set `A = {h(1), …, h(m)}` of `k`-qubit
interactions with distinct binary tags `x(j)` of length `ℓ = ⌈log₂ m⌉`, and a check penalty `∆`,
eq. (28) is
`h̃_unp(v1..vk, u1..uℓ+2) = (1/(ℓ+1)) Σ_j h(j)_{v} ⊗ Π^{x(j)_1}_{u1} ⊗ ⋯ ⊗ Π^{x(j)_ℓ}_{uℓ} ⊗ I
  + ∆ (I ⊗ h_check(uℓ+1, uℓ+2))`.
For a target `K = Σ_{i=1}^M h(j_i)_{V_i}` each occurrence `i` gets a dedicated block of `ℓ+1`
auxiliary pairs; `K̃ = Σ_i Σ_{r=1}^{ℓ+1} h̃_unp(V_i, U_i^{(r)})`, where "the r-th pair occupies the two
check positions and the remaining ℓ pairs encode the tag of h(j_i)": selector position `s` receives
the first qubit (state `|0⟩`) or the second qubit (state `|1⟩`) of its pair according to the tag bit.
The valid configuration is `(01)^{M(ℓ+1)}`, `V|ψ⟩ = |ψ⟩ ⊗ |Ω⟩_A`, and
`K̃(z) = (I_W ⊗ ⟨z|) K̃ (I_W ⊗ |z⟩)`.

**Formalization Note**
* The working register is `Fin NW`; the auxiliary register is `Fin M × Fin (ℓ+1) × Fin 2`: qubit
  `(i, q, b)` is qubit `b` of pair `q` of block `i`. The whole register is the disjoint union.
* In application `r` of block `i`, selector position `s ∈ Fin ℓ` uses pair `r.succAbove s` (the
  pairs other than `r`, in order) and check positions use pair `r`.
* The tags are an arbitrary injective map `Fin m → (Fin ℓ → Fin 2)`; the paper only asks them to be
  distinct.
* `J = max_j ‖h(j)‖` is the supremum over the finite index set of operator norms (the published
  `SYKEdge.opNorm`); it is `0` for `m = 0`. `∆ = 2J + γ` is passed in by the theorem. -/

/-- The selector length `ℓ = ⌈log₂ m⌉`. -/
def selLen (m : ℕ) : ℕ := Nat.clog 2 m

/-- `J = max_j ‖h(j)‖`. -/
noncomputable def maxNorm {k m : ℕ} (A : Fin m → Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ) : ℝ :=
  ⨆ j, SYKEdge.opNorm (A j)

/-- The interaction `h̃_unp` of eq. (28) on `k + ℓ + 2` qubits. -/
noncomputable def hUnp {k m : ℕ} (A : Fin m → Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ)
    (tag : Fin m → Fin (selLen m) → Fin 2) (Δ : ℝ) :
    Matrix (Fin (k + selLen m + 2) → Fin 2) (Fin (k + selLen m + 2) → Fin 2) ℂ :=
  (1 / ((selLen m : ℂ) + 1)) •
      (∑ j, tensorQ (tensorQ (A j) (basisProj (tag j)))
        (1 : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ)) +
    (Δ : ℂ) • tensorQ (1 : Matrix (Fin (k + selLen m) → Fin 2) (Fin (k + selLen m) → Fin 2) ℂ)
      hCheck

/-- The register: working qubits `Fin NW` and auxiliary qubits `(block, pair, position)`. -/
abbrev CompReg (NW M m : ℕ) : Type := Fin NW ⊕ (Fin M × Fin (selLen m + 1) × Fin 2)

/-- The ordered tuple of application `r` of block `i`. -/
def compTuple {k m NW M : ℕ} (tag : Fin m → Fin (selLen m) → Fin 2) (V : Fin M → Fin k → Fin NW)
    (jj : Fin M → Fin m) (i : Fin M) (r : Fin (selLen m + 1)) :
    Fin (k + selLen m + 2) → CompReg NW M m :=
  Fin.append (Fin.append (fun q => Sum.inl (V i q))
      (fun s => Sum.inr (i, r.succAbove s, tag (jj i) s)))
    ![Sum.inr (i, r, 0), Sum.inr (i, r, 1)]

/-- The compiled Hamiltonian `K̃ = Σ_i Σ_r h̃_unp(V_i, U_i^{(r)})`. -/
noncomputable def compHam {k m NW M : ℕ} (A : Fin m → Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ)
    (tag : Fin m → Fin (selLen m) → Fin 2) (Δ : ℝ) (V : Fin M → Fin k → Fin NW)
    (jj : Fin M → Fin m) :
    Matrix (CompReg NW M m → Fin 2) (CompReg NW M m → Fin 2) ℂ :=
  ∑ i, ∑ r, onTuple (hUnp A tag Δ) (compTuple tag V jj i r)

/-- The target `K = Σ_i h(j_i)_{V_i}` on the working register. -/
noncomputable def targetHam {k m NW M : ℕ} (A : Fin m → Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ)
    (V : Fin M → Fin k → Fin NW) (jj : Fin M → Fin m) :
    Matrix (Fin NW → Fin 2) (Fin NW → Fin 2) ℂ :=
  ∑ i, onTuple (A (jj i)) (V i)

/-- The valid auxiliary configuration `z_val = (01)^{M(ℓ+1)}`. -/
def zVal (M m : ℕ) : Fin M × Fin (selLen m + 1) × Fin 2 → Fin 2 := fun a => a.2.2

/-- The isometry `V|ψ⟩ = |ψ⟩ ⊗ |Ω⟩_A` as a matrix. -/
def validIso (NW M m : ℕ) : Matrix (CompReg NW M m → Fin 2) (Fin NW → Fin 2) ℂ :=
  fun s w => if (fun q => s (Sum.inl q)) = w ∧ (fun a => s (Sum.inr a)) = zVal M m then 1 else 0

/-- The operator induced on the working register in the auxiliary sector `z`. -/
def sectorOp {NW M m : ℕ} (Kt : Matrix (CompReg NW M m → Fin 2) (CompReg NW M m → Fin 2) ℂ)
    (z : Fin M × Fin (selLen m + 1) × Fin 2 → Fin 2) :
    Matrix (Fin NW → Fin 2) (Fin NW → Fin 2) ℂ :=
  fun w w' => Kt (Sum.elim w z) (Sum.elim w' z)

/-- The pinned-compiler isometry `V|ψ⟩ = |ψ⟩_W ⊗ |Ψ_ancilla⟩_A` (§4.1.3, p.38) for a working
register `Fin NW` and a pinned auxiliary register `Fin p` in the state `Ψ`. -/
noncomputable def pinnedIso (NW p : ℕ) (Ψ : EuclideanSpace ℂ (Fin p → Fin 2)) :
    Matrix ((Fin NW ⊕ Fin p) → Fin 2) (Fin NW → Fin 2) ℂ :=
  fun s w => (if (fun q => s (Sum.inl q)) = w then 1 else 0) * Ψ (fun a => s (Sum.inr a))

end Supplement

end SingleInteraction


