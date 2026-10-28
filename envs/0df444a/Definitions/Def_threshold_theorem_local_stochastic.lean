-- Prove2me | Definitions.Def_threshold_theorem_local_stochastic
-- name    : threshold_theorem_local_stochastic
-- status  : Definition
-- author  : @shivm
-- created : 2026-10-25T20:31:31.197467+00:00
-- url     : https://prove2.me/theorems/210034f9-daea-409f-86b5-4057745aa687
-- title:
--   Local stochastic noise (with environment), push-forwards and qubit relabelling for layered circuits
-- statement:
--   Auxiliary notions for the concatenated (level-$k$) proof of the quantum threshold theorem, built on the layered circuit model `threshold_theorem_noise_model`.
--
--   **Local stochastic noise with an environment.** For a circuit $C$ on qubits $Q$, a location is a pair $(t,j)$ (layer $t$, position $j$ in that layer). Given a fault set $F$ of locations and fault channels, `faultyState F fault C` runs $C$ on the data qubits $Q$ together with $m$ environment qubits, all initialised to $|0\rangle$: a location $(t,j)\notin F$ applies its ideal operation to its own qubits, and a location $(t,j)\in F$ applies an arbitrary channel `fault t j k` jointly to its $k$ qubits and the whole environment. Because the environment carries memory, faults can be correlated in time and chosen adversarially. `dataOutDist` is the distribution of a computational-basis measurement of the data qubits, with the environment traced out.
--
--   `IsLocalStochasticDist C e P` says that $P$ is the output distribution of $C$ under some local stochastic noise process of rate $e$. That is, $P=\sum_i w_i\,\mathrm{dataOutDist}(\mathrm{faultyState}(F_i,\mathrm{fault}_i,C))$ is a finite mixture with probability weights $w_i$, and for every set $S$ of locations
--   $$\Pr[S\subseteq F]=\sum_{i:\,S\subseteq F_i} w_i\;\le\; e^{|S|}.$$
--   This is the local stochastic error model of Gottesman (arXiv:0904.2557, Sec. 5, Def. of local stochastic noise, used in Theorem 10) and Aliferis–Gottesman–Preskill (quant-ph/0504218, Sec. 5). It is the noise class that stays closed under level reduction, which is why the recursion in the threshold theorem needs it.
--
--   **Push-forward, block decoding, relabelling.** `pushDist f P` is the push-forward $y\mapsto\sum_{f(x)=y}P(x)$. `blockMap dec` decodes a bit string on $Q\times\mathrm{Fin}\,b$ to one bit per $q\in Q$ by applying `dec` to each block, so `decodeDist dec P` is `pushDist (blockMap dec) P`. `Circuit.relabel σ` renames the qubits of a circuit along a bijection $\sigma:Q\simeq Q'$ and keeps the same layers and location order.
-- source:
--   D. Gottesman, An Introduction to Quantum Error Correction and Fault-Tolerant Quantum Computation, arXiv:0904.2557, Section 5 (local stochastic error model, Theorem 10); P. Aliferis, D. Gottesman, J. Preskill, Quantum accuracy threshold for concatenated distance-3 codes, Quant. Inf. Comput. 6 (2006), quant-ph/0504218, Sec. 5 (local stochastic noise, level reduction). Built on Prove2Me definition threshold_theorem_noise_model.

import Mathlib
import Definitions.Def_threshold_theorem_noise_model

/-!
# Local stochastic noise with a quantum environment, push-forwards and qubit relabelling

Auxiliary notions for the concatenated (level-k) threshold argument, built on
`Definitions.Def_threshold_theorem_noise_model`.
-/

open Matrix

namespace ThresholdTheorem

/-! ## Push-forwards, block decoding and relabelling -/

open Classical in
/-- Push-forward of a function `P : α → ℝ` (e.g. a probability distribution) along `f`. -/
noncomputable def pushDist {α β : Type*} [Fintype α] (f : α → β) (P : α → ℝ) : β → ℝ :=
  fun y => ∑ x ∈ Finset.univ.filter (fun x => f x = y), P x

/-- Blockwise decoding of a measured bit string on `Q × Fin b` to one bit per `q : Q`. -/
def blockMap {Q : Type*} {b : ℕ} (dec : (Fin b → Fin 2) → Fin 2) (x : Q × Fin b → Fin 2) :
    Q → Fin 2 :=
  fun q => dec (fun j => x (q, j))

/-- Relabel the qubits of a location along a bijection. -/
def Location.relabel {Q Q' : Type*} (σ : Q ≃ Q') (ℓ : Location Q) : Location Q' :=
  ⟨ℓ.op, ℓ.support.trans σ.toEmbedding⟩

/-- Relabel the qubits of a layer along a bijection. -/
def Layer.relabel {Q Q' : Type*} [DecidableEq Q] [DecidableEq Q'] (σ : Q ≃ Q') (L : Layer Q) :
    Layer Q' :=
  ⟨L.locs.map (Location.relabel σ), by
    intro q
    have h : ((L.locs.map (Location.relabel σ)).flatMap fun ℓ => List.ofFn ℓ.support) =
        (L.locs.flatMap fun ℓ => List.ofFn ℓ.support).map σ := by
      simp [List.flatMap_map, List.map_flatMap, Location.relabel, List.map_ofFn,
        Function.comp_def]
      rfl
    rw [h]
    have hq : q = σ (σ.symm q) := (σ.apply_symm_apply q).symm
    rw [hq, List.count_map_of_injective _ _ σ.injective]
    exact L.partition _⟩

/-- Relabel the qubits of a circuit along a bijection (same layers, same location order). -/
def Circuit.relabel {Q Q' : Type*} [DecidableEq Q] [DecidableEq Q'] (σ : Q ≃ Q')
    (C : Circuit Q) : Circuit Q' :=
  C.map (Layer.relabel σ)

/-! ## Local stochastic noise with a quantum environment -/

/-- The qubits of a location followed by `m` environment qubits, inside `Q ⊕ Fin m`. -/
def envEmbed {Q : Type*} {k : ℕ} (m : ℕ) (s : Fin k ↪ Q) : Fin (k + m) ↪ Q ⊕ Fin m :=
  ⟨Fin.addCases (fun i => Sum.inl (s i)) (fun j => Sum.inr j), by
    intro a b hab
    induction a using Fin.addCases <;> induction b using Fin.addCases <;>
      simp_all [Fin.addCases_left, Fin.addCases_right, s.injective.eq_iff]⟩

/-- Execution of layer number `t` on data qubits `Q` plus `m` environment qubits, where the
locations `(t, j) ∈ F` are faulty and apply the channel `fault t j k` jointly to their `k`
qubits and the environment, while all other locations act ideally on their own qubits. -/
noncomputable def faultyLayer {Q : Type*} [Fintype Q] [DecidableEq Q] {m : ℕ}
    (F : Finset (ℕ × ℕ)) (fault : ℕ → ℕ → (k : ℕ) → Channel (k + m)) (t : ℕ) (L : Layer Q)
    (ρ : Op (Q ⊕ Fin m)) : Op (Q ⊕ Fin m) :=
  L.locs.zipIdx.foldl
    (fun σ ℓj =>
      if (t, ℓj.2) ∈ F then
        applyKraus (envEmbed m ℓj.1.support) (fault t ℓj.2 ℓj.1.op.arity).kraus σ
      else
        applyKraus (ℓj.1.support.trans Function.Embedding.inl) ℓj.1.op.idealKraus σ)
    ρ

/-- Final state of the execution of `C` with fault set `F` and fault channels `fault`,
started in `|0…0⟩` on data and environment. -/
noncomputable def faultyState {Q : Type*} [Fintype Q] [DecidableEq Q] {m : ℕ}
    (F : Finset (ℕ × ℕ)) (fault : ℕ → ℕ → (k : ℕ) → Channel (k + m)) (C : Circuit Q) :
    Op (Q ⊕ Fin m) :=
  C.zipIdx.foldl (fun σ Lt => faultyLayer F fault Lt.2 Lt.1 σ) (initState (Q ⊕ Fin m))

/-- Outcome distribution of measuring the data qubits (environment traced out). -/
noncomputable def dataOutDist {Q : Type*} {m : ℕ} (ρ : Op (Q ⊕ Fin m)) : (Q → Fin 2) → ℝ :=
  fun x => ∑ y : Fin m → Fin 2, (ρ (Sum.elim x y) (Sum.elim x y)).re

/-- `P` is the measured output distribution of the circuit `C` under some **local stochastic**
noise process of rate `e`: a finite mixture (weights `w`) of executions in which a random fault
set `F` is faulty, with `Pr[S ⊆ F] ≤ e ^ |S|` for every set `S` of locations `(t, j)`, and the
faulty locations act by arbitrary (adversarial, environment-correlated) channels. -/
def IsLocalStochasticDist {Q : Type*} [Fintype Q] [DecidableEq Q] (C : Circuit Q) (e : ℝ)
    (P : (Q → Fin 2) → ℝ) : Prop :=
  ∃ (r m : ℕ) (w : Fin r → ℝ) (F : Fin r → Finset (ℕ × ℕ))
    (fault : Fin r → ℕ → ℕ → (k : ℕ) → Channel (k + m)),
    (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
    (∀ S : Finset (ℕ × ℕ), ∑ i ∈ Finset.univ.filter (fun i => S ⊆ F i), w i ≤ e ^ S.card) ∧
    P = fun x => ∑ i, w i * dataOutDist (faultyState (F i) (fault i) C) x

end ThresholdTheorem


