-- Prove2me | Definitions.Def_QCollLB_Verification
-- name    : QCollLB_Verification
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:16:24.41126+00:00
-- url     : https://prove2.me/theorems/fbe829c7-d9ac-407a-ab15-f0d5e1159c61
-- title:
--   Definition 5.21, p.42–45 — target projectors, the $k$-step verification process, collision-count projectors and $p_{\mathrm{succ}}$
-- statement:
--   For a family $\mathcal B$ of $k$-element target sets, $P_{\mathrm{full}}=\sum_{d:\ \exists B\in\mathcal B,\ B\subseteq\mathrm{Im}\,d}|d\rangle\langle d|$ on $D$, and $P_{\mathrm{ver}}$ projects onto "the proposed positions $i_1,\dots,i_k$ are distinct and the returned slots $\{y_1,\dots,y_k\}$ form a target in $\mathcal B$".
--
--   **Verification process.** Starting from $\eta_0\in D_{\le t}\otimes A$ storing a proposed ordered tuple, add $k$ fresh answer registers in state $|0\rangle$. Check $j$ ($j=1,\dots,k$): on branches with distinct proposed positions, query position $i_j$ into answer register $j$ with the unprojected auxiliary value query $C_{i_j}E_{i_j}C_{i_j}$, where $E_i|z,d\rangle=|z+d(i),d\rangle$ (blank $=0$); on rejecting branches make a dummy query. $\eta_j$ is the state after $j$ checks; nothing is renormalized.
--
--   **Collision counts.** For public buckets, $m_y(d)=|\mathrm{Im}\,d\cap B_y|$ and $L_j(d)=|\{y:m_y(d)\ge j\}|$; $P_{j,\ge\ell},P_{j,=\ell},P_{j,\le\ell}$ are the diagonal projectors of the corresponding events.
--
--   **Success.** For a joint state $\psi\in A\otimes P$ with a stored tuple, $p_{\mathrm{succ}}=\|\Pi_{\mathrm{succ}}\psi\|^2$, where $\Pi_{\mathrm{succ}}$ projects onto "the tuple has distinct entries and $\pi(\text{tuple})=B_y$ for some $y$".
--
--   **Formalization Note** $L_j$ is the published `MultiCollQ.levelCount`. Positions in `Fin n` are always valid, so a rejecting branch is one with a repeated position; the dummy query is the identity. Register order is $((\text{tuple},w),(\text{answers},d))$.
-- source:
--   Peng–Wu, Quantum Lower Bounds for Collision Problems, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Definition 5.21 p.41, p.42, p.43, p.45

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_MultiCollQ_levelCount
import Definitions.Def_QCollLB_Buckets
import Definitions.Def_QCollLB_Harmonic

namespace QCollLB

open CompPermOracle

/-- The diagonal projector `P_E = Σ_{x : E(x)} |x⟩⟨x|` of an event `E` on basis labels
(Peng–Wu, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Eq. (2), p.13). -/
noncomputable def eventProj {X : Type*} [Fintype X] [DecidableEq X] (E : X → Prop)
    [DecidablePred E] : Hil X →L[ℂ] Hil X :=
  ∑ x ∈ Finset.univ.filter E, ketBra (ket x) (ket x)

/-- `P_full = Σ_{d : ∃ B ∈ 𝓑, B ⊆ Im d} |d⟩⟨d|` on `D`, for a target family `𝓑`
(arXiv:2611.01767, Definition 5.21, p.41). -/
noncomputable def Pfull {n : ℕ} (𝓑 : Finset (Finset (Fin n))) :
    Hil (PartialPerm n) →L[ℂ] Hil (PartialPerm n) := by
  classical
  exact eventProj fun d : PartialPerm n => ∃ B ∈ 𝓑, B ⊆ imSet d

/-- The threshold projector `Σ_{d : E(L_j(d))} |d⟩⟨d|` on `D` for a condition `E` on the collision
count `L_j(d) = |{y : m_y(d) ≥ j}|`, `m_y(d) = |Im d ∩ B_y|` (arXiv:2611.01767, p.43:
`P_{j,≥ℓ}`, `P_{j,=ℓ}`, `P_{j,≤ℓ}`).

**Formalization Note.** `L_j(d)` is the published `MultiCollQ.levelCount b j d` (with `m_y(d)` its
`occ b d y`), for the bucket label map `b : Fin n → Fin N`. -/
noncomputable def threshProj {n N : ℕ} (b : Fin n → Fin N) (j : ℕ) (E : ℕ → Prop)
    [DecidablePred E] : Hil (PartialPerm n) →L[ℂ] Hil (PartialPerm n) :=
  eventProj fun d : PartialPerm n => E (MultiCollQ.levelCount b j d)

/-- The value of the database at position `i` as an answer symbol of `Z_{n+1}`: `0` (blank) if
`i ∉ Dom d`, and the slot `d(i)` otherwise (arXiv:2611.01767, Definition 3.2, p.19; p.42: "valid
slots are `1, …, n`, and the blank symbol is `0`").

**Formalization Note.** The 0-based slot `u : Fin n` is stored as `u + 1`. -/
def slotVal {n : ℕ} (d : PartialPerm n) (i : Fin n) : ZMod (n + 1) :=
  match d i with
  | none => 0
  | some u => (((u : ℕ) + 1 : ℕ) : ZMod (n + 1))

/-- The slot named by an answer symbol `z ∈ Z_{n+1}`: `none` for the blank `0`, and the 0-based
slot `z − 1` otherwise (inverse of the encoding in `slotVal`). -/
def slotOf {n : ℕ} (z : ZMod (n + 1)) : Option (Fin n) :=
  if h : 0 < z.val then some ⟨z.val - 1, by have := ZMod.val_lt z; omega⟩ else none

/-- The additive (value) form of the database evaluation at position `i` into answer register
`j`: `|a, d⟩ ↦ |a + slotVal(d, i)·e_j, d⟩` on `ℂ[Z_{n+1}^k] ⊗ D` (arXiv:2611.01767, §5.1, p.23:
"Auxiliary value queries refer to the Fourier-equivalent additive form of the same operation"). -/
noncomputable def valShift {n k : ℕ} (i : Fin n) (j : Fin k) :
    Hil ((Fin k → ZMod (n + 1)) × PartialPerm n) →L[ℂ]
      Hil ((Fin k → ZMod (n + 1)) × PartialPerm n) :=
  ∑ p : (Fin k → ZMod (n + 1)) × PartialPerm n,
    ketBra (ket (Function.update p.1 j (p.1 j + slotVal p.2 i), p.2)) (ket p)

/-- The unprojected auxiliary value query at position `i` into answer register `j`:
`(I ⊗ C_i) E_{i,j} (I ⊗ C_i)` with `E_{i,j}` = `valShift i j` (arXiv:2611.01767, Definition 5.3,
p.23, in its additive form; p.42). `C_i` is `CompPermOracle.compressU i`. -/
noncomputable def auxVal {n k : ℕ} (i : Fin n) (j : Fin k) :
    Hil ((Fin k → ZMod (n + 1)) × PartialPerm n) →L[ℂ]
      Hil ((Fin k → ZMod (n + 1)) × PartialPerm n) :=
  (opTensor (1 : Hil (Fin k → ZMod (n + 1)) →L[ℂ] Hil (Fin k → ZMod (n + 1))) (compressU i)).comp
    ((valShift i j).comp
      (opTensor (1 : Hil (Fin k → ZMod (n + 1)) →L[ℂ] Hil (Fin k → ZMod (n + 1))) (compressU i)))

/-- Check number `j` of the verification process (arXiv:2611.01767, p.42): controlled on the
proposed ordered tuple `τ` (and the rest `w` of the workspace), on valid branches (`τ` has distinct
entries) query position `τ_j` into the fresh answer register `j` with the unprojected auxiliary value
query; on rejecting branches (a repeated position) perform a dummy query.

**Formalization Note.** Register order: `((τ, w), (a, d))` with `τ : Fin k → Fin n` the proposed
positions, `w ∈ W` the rest of `A`, `a : Fin k → Z_{n+1}` the `k` answer registers and `d` the
database. Positions in `Fin n` are always valid, so "invalid or repeated" is "repeated". The dummy
query is the identity; rejecting branches are kept and never renormalized. -/
noncomputable def checkStep {n k : ℕ} (W : Type*) [Fintype W] [DecidableEq W] (j : Fin k) :
    Hil (((Fin k → Fin n) × W) × ((Fin k → ZMod (n + 1)) × PartialPerm n)) →L[ℂ]
      Hil (((Fin k → Fin n) × W) × ((Fin k → ZMod (n + 1)) × PartialPerm n)) := by
  classical
  exact controlled fun c : (Fin k → Fin n) × W =>
    if Function.Injective c.1 then auxVal (c.1 j) j else 1

/-- The whole verification process `η_0 ↦ η_k`: checks `1, …, k` in this order (arXiv:2611.01767,
p.42: "Write `η_j` for the state after `j` checks"). -/
noncomputable def verifyOp {n k : ℕ} (W : Type*) [Fintype W] [DecidableEq W] :
    Hil (((Fin k → Fin n) × W) × ((Fin k → ZMod (n + 1)) × PartialPerm n)) →L[ℂ]
      Hil (((Fin k → Fin n) × W) × ((Fin k → ZMod (n + 1)) × PartialPerm n)) :=
  (List.finRange k).foldl (fun acc j => (checkStep W j).comp acc) 1

/-- Adjoining the `k` fresh answer registers, initialized to `|0⟩`, to a state of `A ⊗ D` with
`A = ℂ[[n]^k] ⊗ W` (arXiv:2611.01767, p.42: "into `k` fresh answer registers"). -/
noncomputable def freshAns {n k : ℕ} (W : Type*) [Fintype W] [DecidableEq W] :
    Hil (((Fin k → Fin n) × W) × PartialPerm n) →L[ℂ]
      Hil (((Fin k → Fin n) × W) × ((Fin k → ZMod (n + 1)) × PartialPerm n)) :=
  ∑ p : ((Fin k → Fin n) × W) × PartialPerm n, ketBra (ket (p.1, (0, p.2))) (ket p)

/-- `P_ver = P_{{i_1, …, i_k} ∈ ([n] choose k) ∧ {y_1, …, y_k} ∈ 𝓑}` (arXiv:2611.01767,
Definition 5.21, p.41), as a diagonal projector on the verification register: the proposed positions
are distinct and the returned slots `y_1, …, y_k` (all non-blank) form a target `B ∈ 𝓑`. -/
noncomputable def Pver {n k : ℕ} (W : Type*) [Fintype W] [DecidableEq W]
    (𝓑 : Finset (Finset (Fin n))) :
    Hil (((Fin k → Fin n) × W) × ((Fin k → ZMod (n + 1)) × PartialPerm n)) →L[ℂ]
      Hil (((Fin k → Fin n) × W) × ((Fin k → ZMod (n + 1)) × PartialPerm n)) := by
  classical
  exact eventProj fun x : ((Fin k → Fin n) × W) × ((Fin k → ZMod (n + 1)) × PartialPerm n) =>
    Function.Injective x.1.1 ∧
      ∃ B ∈ 𝓑, Finset.univ.image (fun j => slotOf (x.2.1 j)) = B.image some

/-- `P_full ⊗ I_A` on the verification register (arXiv:2611.01767, Lemma 5.22, Eq. (62), p.42). -/
noncomputable def PfullVer {n k : ℕ} (W : Type*) [Fintype W] [DecidableEq W]
    (𝓑 : Finset (Finset (Fin n))) :
    Hil (((Fin k → Fin n) × W) × ((Fin k → ZMod (n + 1)) × PartialPerm n)) →L[ℂ]
      Hil (((Fin k → Fin n) × W) × ((Fin k → ZMod (n + 1)) × PartialPerm n)) := by
  classical
  exact eventProj fun x : ((Fin k → Fin n) × W) × ((Fin k → ZMod (n + 1)) × PartialPerm n) =>
    ∃ B ∈ 𝓑, B ⊆ imSet x.2.2

/-- The success projector of Permutation Bucket Finding on `ℂ[[n]^k × W] ⊗ P`: the proposed ordered
tuple `τ` has distinct entries and `π(τ) = B_y` for some bucket (arXiv:2611.01767, Definition 5.23,
p.42; p.45: "let `p_succ` denote the probability that the tuple is a valid output"). -/
noncomputable def succProj {n N k : ℕ} (W : Type*) [Fintype W] [DecidableEq W]
    (b : Fin n → Fin N) :
    Hil (((Fin k → Fin n) × W) × Equiv.Perm (Fin n)) →L[ℂ]
      Hil (((Fin k → Fin n) × W) × Equiv.Perm (Fin n)) := by
  classical
  exact eventProj fun x : ((Fin k → Fin n) × W) × Equiv.Perm (Fin n) =>
    Function.Injective x.1.1 ∧ ∃ y, Finset.univ.image (fun j => x.2 (x.1.1 j)) = bucket b y

/-- `p_succ = ‖Π_succ ψ‖²`, the probability that the stored tuple is a valid output of Permutation
Bucket Finding in the joint state `ψ ∈ A ⊗ P` (arXiv:2611.01767, p.45). -/
noncomputable def psucc {n N k : ℕ} (W : Type*) [Fintype W] [DecidableEq W] (b : Fin n → Fin N)
    (ψ : Hil (((Fin k → Fin n) × W) × Equiv.Perm (Fin n))) : ℝ :=
  ‖succProj W b ψ‖ ^ 2

end QCollLB


