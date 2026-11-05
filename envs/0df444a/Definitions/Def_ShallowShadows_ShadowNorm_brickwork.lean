-- Prove2me | Definitions.Def_ShallowShadows_ShadowNorm_brickwork
-- name    : ShallowShadows_ShadowNorm_brickwork
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:34:21.448351+00:00
-- url     : https://prove2.me/theorems/d26b380e-a3df-44d6-884d-ceca9c6f47be
-- title:
--   The depth-$d$ shallow-shadow ensemble $\mathcal U_d$ (brickwork, $d\in\mathbb N$)
-- statement:
--   On $n = 2m$ qubits and for a depth $d \in \{0, 1, 2, \dots\}$, a unitary $U \sim \mathcal U_d$ is sampled by
--
--   1. applying an independent uniformly random single-qubit Clifford gate to each qubit (the $0$th layer $L_0$), then
--   2. for each layer $i = 1, \dots, d$, applying independent uniformly random two-qubit Clifford gates in the circular brickwork pattern (layer $L_i$).
--
--   The resulting unitary is $U = L_d \cdots L_1 L_0$. For $d = 0$ this is the random Pauli measurement scheme of Huang, Kueng and Preskill.
--
--   **Formalization Note** The ensemble is a finite weighted family of unitaries (`ClassicalShadow.Linear.Primitive`), indexed by the labels of all gates, with uniform weights over Cliffords modulo global phase. Its measurement channel $\mathcal M_d$ is the reused HKP channel of Eq. (2).
-- source:
--   Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, Shallow shadows: Expectation estimation using low-depth random Clifford circuits, arXiv:2209.12924v3, §V, p. 4, Fig. 1

import Mathlib
import Definitions.Def_ShallowShadows_ShadowNorm_CliffordLabel
import Definitions.Def_ShallowShadows_ShadowNorm_uniformDist
import Definitions.Def_ShallowShadows_ShadowNorm_embedGate
import Definitions.Def_ShallowShadows_ShadowNorm_brickPair

open ClassicalShadow.Linear

namespace ShallowShadows.ShadowNorm

/-- Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, *Shallow shadows: Expectation
estimation using low-depth random Clifford circuits*, arXiv:2209.12924v3, §V, p. 4 and Fig. 1:
the depth-`k` ensemble `𝒰_k = (𝕌_k, μ_k)` on `n = 2m` qubits. "We sample from `𝒰_d` by first
applying a uniformly random single qubit Clifford gate to each qubit (the 0th layer) then for each
layer `i ∈ [d]` we apply uniformly randomly chosen two qubit Clifford gates in a nearest-neighbour
circular brickwork pattern applied to `n` (even) qubits in a circle".

A label `ℓ = (c, g)` consists of a single-qubit Clifford label `c j` for every qubit `j` and a
two-qubit Clifford label `g l p` for every layer `l` and every gate `p` of that layer; labels are
drawn uniformly. The unitary is `U(ℓ) = L_k ⋯ L_1 L_0`, where `L_0 = ⊗_j rep(c j)` and `L_{l+1}` is
the product over `p` of `rep(g l p)` embedded on the pair `brickPair m l p`. For `k = 0` this is
the random Pauli measurement ensemble `𝒰_0` of Huang–Kueng–Preskill.

**Formalization Note.** (1) Uniform over Cliffords means uniform over Cliffords modulo global phase
(`CliffordLabel`), with the finiteness of `CliffordLabel 1` and `CliffordLabel 2` taken as
instance arguments. (2) `n` even is encoded as `n = 2m`. (3) Layers are indexed from `0`
(`l : Fin k` is the paper's layer `l + 1`); the gates of one layer act on disjoint pairs, so their
order within the layer (here increasing `p`) does not matter. (4) The ensemble is a reused HKP
measurement primitive `ClassicalShadow.Linear.Primitive`, so the measurement channel `M_d` of
Eq. (2) is `ClassicalShadow.Linear.measChannel (brickwork m k)`. -/
noncomputable def brickwork (m k : ℕ) [Fintype (CliffordLabel 1)] [Fintype (CliffordLabel 2)] :
    Primitive (2 * m) ((Fin (2 * m) → CliffordLabel 1) × (Fin k → Fin m → CliffordLabel 2)) where
  w := uniformDist _
  U ℓ :=
    (List.ofFn (fun l : Fin k =>
        (List.ofFn (fun p : Fin m => embedGate (brickPair m l.val p) (ℓ.2 l p).rep)).prod)).reverse.prod *
      (List.ofFn (fun j : Fin (2 * m) =>
        embedGate (⟨fun _ => j, fun a b _ => Subsingleton.elim a b⟩ : Fin 1 ↪ Fin (2 * m))
          (ℓ.1 j).rep)).prod

end ShallowShadows.ShadowNorm


