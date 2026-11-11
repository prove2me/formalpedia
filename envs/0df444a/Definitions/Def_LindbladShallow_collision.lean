-- Prove2me | Definitions.Def_LindbladShallow_collision
-- name    : LindbladShallow_collision
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:19:46.07612+00:00
-- url     : https://prove2.me/theorems/92a96e99-e5b9-4452-a3b5-69ab5cb53595
-- title:
--   Collision circuits, restrictions and the fresh-bath period channel
-- statement:
--   Fix an input and a segment of $M$ periods with time step $h$. The **jump-occurrence labels** are $\mathcal B_J=\{(e,m):e\in I_J,\ 0\le m<M\}$ and the segment's space is $\mathcal H_S\otimes\bigotimes_{b\in\mathcal B_J}\mathbb C^{d_E}_b$ with $d_E=2^{\lceil\log_2(1+\mu_*)\rceil}$; $E_0\psi=\psi\otimes\bigotimes_b|0\rangle_b$. Occurrence $(e,m)$ applies $V_{H_e,h}$ to the system (retained $e\in I_H$), or $V_{J_e,h}$ to the system and bath $(e,m)$ (retained $e\in I_J$), $J_e$ padded with zero jumps to $d_E$.
--
--   A **collision word** is a chronological list of occurrences, each forward or adjoint; its unitary is the ordered product. The **restricted collision circuit** $U_{\mathcal T,\Omega}$ applies, period by period in the prescribed term order, the occurrences of the active terms $\mathcal T$ whose support lies in $\Omega$ (the others are identities). The **period channel** $\Phi_h$ applies, in term order, $\mathrm{Ad}\,V_{H_e,h}$ or the reduced channel of $V_{J_e,h}$ with a fresh vacuum bath.
--
--   These are the collision unitaries of §2.3, used in Lemma A.4 and in the spatial decomposition (Theorem 3.4, Corollary 3.5, Theorem 3.7).
--
--   **Formalization Note** Since distinct jump occurrences use distinct baths, the forward fresh-label circuit over $m$ periods induces $\Phi_h^m$ (p.12–13); the channel is written in that composed form.
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), §2.3, pp.11–12; Eq. (8), p.13

import Mathlib
import Definitions.Def_LindbladShallow_Instance
import Definitions.Def_LindbladShallow_occupation

open scoped Matrix ComplexOrder

namespace LindbladShallow

/-- `d_E − 1`, where `d_E := 2^{⌈log₂(1 + µ∗)⌉}` is the padded bath dimension
(arXiv:2610.05362, held version sha256 8f4637ef…, §2.3, p.12). The bath basis is `Fin (d_E)`,
value `0` the vacuum. -/
def dEm1 (P : Params) : ℕ := 2 ^ Nat.clog 2 (1 + P.μstar) - 1

/-- The stacked jump map `J_e ψ = Σ_µ |µ⟩ L_eµ ψ` of a term, padded with zero jumps to the bath
dimension (p.9 and p.12): component `µ` (0-based) is the bath value `µ + 1`; it is `0` for a
Hamiltonian term. -/
noncomputable def Jloc {P : Params} (t : Term P) :
    Matrix (Fin (dEm1 P) × LocBasis P.d0 t.supp.length) (LocBasis P.d0 t.supp.length) ℂ :=
  Matrix.of fun p s => if h : p.1.val < t.jumpsC.length then (t.jumpsC.get ⟨p.1.val, h⟩) p.2 s
    else 0

/-- The jump-occurrence labels of a segment of `M` periods, `B_J := {(e, m) : e ∈ I_J, 0 ≤ m < M}`
over the retained dissipative terms (p.12). -/
def BJ {P : Params} (I : Instance P) (M : ℕ) :=
  {b : Fin I.nT × Fin M // (I.term b.1).IsJump ∧ (I.term b.1).Retained}

noncomputable instance {P : Params} (I : Instance P) (M : ℕ) : Fintype (BJ I M) := by
  classical
  unfold BJ
  infer_instance

noncomputable instance {P : Params} (I : Instance P) (M : ℕ) : DecidableEq (BJ I M) := by
  classical
  unfold BJ
  infer_instance

/-- The common system–environment basis of a segment: the system and one bath of dimension `d_E`
per jump-occurrence label, `ℋ_S ⊗ ⨂_{b ∈ B_J} ℂ^{d_E}_b` (p.12). -/
abbrev Tot {P : Params} (I : Instance P) (M : ℕ) := OccSp (Sys I) (BJ I M) (dEm1 P)

/-- The vacuum initialization `E₀ψ := ψ ⊗ ⨂_{b ∈ B_J} |0⟩_b` of a segment (p.12). -/
noncomputable def E0 {P : Params} (I : Instance P) (M : ℕ) : Matrix (Tot I M) (Sys I) ℂ :=
  vacOcc

/-- The collision gate of occurrence `(e, m)` with time step `h` (arXiv:2610.05362, §2.3, p.12):
for a retained Hamiltonian term, `V_{H_e,h} = (I − ihH_e/2)(I + ihH_e/2)^{−1}` on the system only;
for a retained dissipative term, `V_{J_e,h} = (I − i√h G_{J_e}/2)(I + i√h G_{J_e}/2)^{−1}` on the
system and bath `(e, m)`; the identity for a removed term (removed by preprocessing). -/
noncomputable def occGate {P : Params} (I : Instance P) (M : ℕ) (h : ℝ) (e : Fin I.nT)
    (m : Fin M) : Matrix (Tot I M) (Tot I M) ℂ :=
  open Classical in
  if hJ : (I.term e).IsJump ∧ (I.term e).Retained then
    onBath (⟨(e, m), hJ⟩ : BJ I M) (liftSysX I (I.term e).supp (cayleyJ h (Jloc (I.term e))))
  else if (I.term e).Retained then
    sysOnly (liftSys I (I.term e).supp (cayley ((h : ℂ) • (I.term e).hamC)))
  else 1

/-- A collision word: a chronological list of occurrences `(e, m)`, each applied forward
(`false`) or as its adjoint (`true`, "the adjoint of the same gate on the same system and bath",
p.12). -/
abbrev Word {P : Params} (I : Instance P) (M : ℕ) := List (Fin I.nT × Fin M × Bool)

/-- The unitary of a collision word, head first. -/
noncomputable def wordU {P : Params} (I : Instance P) (M : ℕ) (h : ℝ) (w : Word I M) :
    Matrix (Tot I M) (Tot I M) ℂ :=
  orderedProd (w.map fun x => if x.2.2 then (occGate I M h x.1 x.2.1)ᴴ else occGate I M h x.1 x.2.1)

/-- The inverse word: reversed order, each gate replaced by its adjoint. -/
def adjWord {P : Params} {I : Instance P} {M : ℕ} (w : Word I M) : Word I M :=
  (w.map fun x => (x.1, x.2.1, !x.2.2)).reverse

/-- The forward collision word over the listed periods (in the given order), in the prescribed
term order within each period, restricted to the active retained terms whose whole support lies
in the region `Ω` (arXiv:2610.05362, p.12: "Restricting a collision circuit to a region Ω retains
an occurrence (e, m) only if its term is active and X_e ⊆ Ω"; dropped occurrences are identities,
so chronological positions and bath labels are preserved). -/
noncomputable def fwdWord {P : Params} (I : Instance P) (M : ℕ) (act : Fin I.nT → Prop)
    (Ω : Set (Site P)) (periods : List (Fin M)) : Word I M :=
  open Classical in
  periods.flatMap fun m =>
    ((List.finRange I.nT).filter fun e =>
      decide (act e ∧ (I.term e).Retained ∧ ∀ x ∈ (I.term e).supp, x ∈ Ω)).map
      fun e => (e, m, false)

/-- The restricted collision circuit `U_{T,Ω}` of one segment: all `M` periods, active terms
`act`, region `Ω` (Eq. (8), p.13). With `Ω = Set.univ` it is the unrestricted `U_T`. -/
noncomputable def collU {P : Params} (I : Instance P) (M : ℕ) (h : ℝ) (act : Fin I.nT → Prop)
    (Ω : Set (Site P)) : Matrix (Tot I M) (Tot I M) ℂ :=
  wordU I M h (fwdWord I M act Ω (List.finRange M))

/-- The system channel of occurrence `e` with an independent fresh vacuum bath
(arXiv:2610.05362, p.12–13 and Lemma A.4): `Ad V_{H_e,h}` for a retained Hamiltonian term,
`Z ↦ Tr_b[V_{J_e,h}(Z ⊗ |0⟩⟨0|_b)V_{J_e,h}†]` for a retained dissipative term, the identity for a
removed term. -/
noncomputable def occChannel {P : Params} (I : Instance P) (h : ℝ) (e : Fin I.nT) :
    QAlgorithms.Superop (Sys I) (Sys I) :=
  open Classical in
  if (I.term e).IsJump ∧ (I.term e).Retained then
    isoChannel (liftSysX I (I.term e).supp (cayleyJ h (Jloc (I.term e))) *
      vacIso (0 : Fin (dEm1 P + 1)))
  else if (I.term e).Retained then
    QAlgorithms.conjSuperop (liftSys I (I.term e).supp (cayley ((h : ℂ) • (I.term e).hamC)))
  else id

/-- `Φ_h`: the reduced system channel of one ordered collision period with independently
initialized jump baths (arXiv:2610.05362, p.12), the occurrence channels composed in term order.

**Formalization Note** Since distinct jump occurrences use distinct baths, the forward
fresh-label circuit over `m_tot` periods, traced at the end, induces `Φ_h^{m_tot}` (p.12–13, and
the proof of Lemma A.4, p.60); the channel is written in this composed form. -/
noncomputable def periodChannel {P : Params} (I : Instance P) (h : ℝ) :
    QAlgorithms.Superop (Sys I) (Sys I) :=
  (List.finRange I.nT).foldl (fun Φ e => occChannel I h e ∘ Φ) id

end LindbladShallow


