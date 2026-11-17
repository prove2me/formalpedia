-- Prove2me | Definitions.Def_ExactAmpDich_Supplement_Closure
-- name    : ExactAmpDich_Supplement_Closure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:23:08.813035+00:00
-- url     : https://prove2.me/theorems/7ac490b2-6c97-4587-abad-1daa0110386a
-- title:
--   The library $G\cup\{V_1,\dots,V_r\}$, $V\otimes I_{2^{q-k}}$, and projective closure of available words
-- statement:
--   Objects of Appendix K.
--
--   1. $G\cup\{V_1,\dots,V_r\}$ is the library whose gates are those of $G$, in order, followed by $V_1,\dots,V_r$ on $k_1,\dots,k_r\ge1$ qubits.
--   2. For a $k$-qubit matrix $V$ and $k\le q$, $V\otimes I_{2^{q-k}}$ acts by $V$ on the first $k$ of $q$ qubits and as the identity on the others.
--   3. Fix a finite alphabet $\Omega$ of $2^q\times2^q$ matrices. An **available word** is a product of letters of $\Omega$, the empty word being $I_{2^q}$. The projective class $\pi(V)$ of $V$ lies in the **projective closure** of the available words if there are available words $w_j$ and scalars $|\zeta_j|=1$ with $\zeta_jw_j\to V$.
-- source:
--   Liu–Meng, A Dichotomy for Exact Quantum Circuit Amplitudes, STOC 2027 submission (held manuscript, sha256 40ad9c68…), App. K, p.76 (PDF p.77)

import Mathlib
import Definitions.Def_ExactAmpDich_Library

set_option autoImplicit false

namespace ExactAmpDich.Supplement

open QAlgorithms

/-- The library `G ∪ {V₁, …, V_r}`: the gates of `L` (first, in order) followed by the new gates
`V_i` on `kV i ≥ 1` qubits. Liu–Meng, *A Dichotomy for Exact Quantum Circuit Amplitudes*, STOC 2027
submission (held manuscript, sha256 40ad9c68…), Theorem K.1, p.76 (PDF p.77): "AmpZ(G ∪ {V})". -/
def addGates (L : Library) {r : ℕ} (kV : Fin r → ℕ) (hkV : ∀ i, 1 ≤ kV i)
    (V : (i : Fin r) → Matrix (Qubits (kV i)) (Qubits (kV i)) ℂ) : Library where
  t := L.t + r
  k j := (Fin.addCases (motive := fun _ => Σ k : ℕ, Matrix (Qubits k) (Qubits k) ℂ)
    (fun j => ⟨L.k j, L.U j⟩) (fun i => ⟨kV i, V i⟩) j).1
  one_le_k j := by
    refine Fin.addCases (fun j => ?_) (fun i => ?_) j
    · simpa using L.one_le_k j
    · simpa using hkV i
  U j := (Fin.addCases (motive := fun _ => Σ k : ℕ, Matrix (Qubits k) (Qubits k) ℂ)
    (fun j => ⟨L.k j, L.U j⟩) (fun i => ⟨kV i, V i⟩) j).2

/-- `V ⊗ I_{2^{q−k}}`: a `k`-qubit matrix acting on the first `k` of `q` qubits, identity on the
last `q − k`. -/
def padId {k q : ℕ} (hkq : k ≤ q) (V : Matrix (Qubits k) (Qubits k) ℂ) :
    Matrix (Qubits q) (Qubits q) ℂ :=
  fun y x => if ∀ i : Fin q, k ≤ i.val → y i = x i then
    V (fun i => y ⟨i.val, lt_of_lt_of_le i.isLt hkq⟩) (fun i => x ⟨i.val, lt_of_lt_of_le i.isLt hkq⟩)
  else 0

/-- `π(V)` lies in the **projective closure** of the available words over the alphabet `Ω`: there
are available words `w_j` (products of letters of `Ω`, the empty word being `I_D`) and scalars
`|ζ_j| = 1` with `ζ_j w_j → V`. Liu–Meng, App. K, p.76: "membership of π(V) in the projective
closure means that there are available words wj and scalars |ζj| = 1 such that ζjwj → V." -/
def InProjClosure {q a : ℕ} (Ω : Fin a → Matrix (Qubits q) (Qubits q) ℂ)
    (V : Matrix (Qubits q) (Qubits q) ℂ) : Prop :=
  ∃ (w : ℕ → List (Fin a)) (ζ : ℕ → ℂ), (∀ n, ‖ζ n‖ = 1) ∧
    Filter.Tendsto (fun n => ζ n • ((w n).map Ω).prod) Filter.atTop (nhds V)

end ExactAmpDich.Supplement


