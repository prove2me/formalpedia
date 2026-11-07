-- Prove2me | Definitions.Def_ShadowBootstrap_twoLayer
-- name    : ShadowBootstrap_twoLayer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:24.499169+00:00
-- url     : https://prove2.me/theorems/2e2563e1-7738-4d08-a38f-a8eca366d386
-- title:
--   The two-layer Clifford ensemble $E_{2L}$ with block size $k$ (Definition 3.1)
-- statement:
--   Let $k$ be an even divisor of $n$, $n = km$. The **two-layer Clifford ensemble** $E_{2L}$ consists of circuits $U = U_2U_1$ (Definition 3.1, p.9):
--
--   1. the first layer $U_1$ applies independent, uniformly random $k$-qubit Clifford unitaries $C_0, \dots, C_{m-1}$ to the contiguous blocks $\{jk, jk+1, \dots, jk+k-1\}$;
--   2. the second layer $U_2$ applies independent, uniformly random $k$-qubit Clifford unitaries $C'_0, \dots, C'_{m-1}$ to the same blocks shifted by $k/2$ qubits with periodic boundary conditions, $\{jk + k/2 + i \bmod n : 0 \le i < k\}$.
--
--   All $2m$ block unitaries are independent and uniform on the $k$-qubit Clifford group $\mathrm{Cl}(k)$.
--
--   This is the measurement ensemble of the paper: Lemmas 3.7 and 3.8 bound its shadow estimators, and the suffix ensembles of Lemma A.2 are built from it.
--
--   **Formalization Note** Cliffords are drawn modulo global phase (`ShallowShadows.ShadowNorm.CliffordLabel`, whose finiteness is an instance argument); every quantity of the paper depends on $U$ only through $X \mapsto UXU^\dagger$. The register has $km$ qubits by construction; evenness of $k$ is a hypothesis of the statements that use it. For $m = 1$ both layers act on all $k$ qubits.
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), Definition 3.1, p.9

import Mathlib
import Definitions.Def_ShallowShadows_ShadowNorm_CliffordLabel
import Definitions.Def_ShallowShadows_ShadowNorm_uniformDist
import Definitions.Def_ShallowShadows_ShadowNorm_embedGate

open ClassicalShadow.Linear ShallowShadows.ShadowNorm

namespace ShadowBootstrap

theorem block_lt {k m j i : ℕ} (hj : j < m) (hi : i < k) : j * k + i < k * m := by
  have : (j + 1) * k ≤ m * k := Nat.mul_le_mul_right k hj
  rw [Nat.mul_comm k m]; nlinarith

/-- Block `j` of the first layer: the qubits `jk, jk+1, …, jk+k−1` of a `km`-qubit register. -/
def blockEmb1 (k m : ℕ) (j : Fin m) : Fin k ↪ Fin (k * m) where
  toFun i := ⟨j.1 * k + i.1, block_lt j.2 i.2⟩
  inj' a b h := Fin.ext (by simpa using congrArg Fin.val h)

/-- Block `j` of the second layer: the qubits `jk + k/2 + i (mod km)`, `i < k`, i.e. block `j` of
the first layer shifted cyclically by `k/2` qubits (`finRotate` is the cyclic shift by one). -/
def blockEmb2 (k m : ℕ) (j : Fin m) : Fin k ↪ Fin (k * m) :=
  (blockEmb1 k m j).trans ((finRotate (k * m)) ^ (k / 2)).toEmbedding

/-- The layer `⊗_j C_j` of independent block Cliffords placed by `e`. -/
noncomputable def blockLayer {k m : ℕ} (e : Fin m → (Fin k ↪ Fin (k * m)))
    (c : Fin m → CliffordLabel k) : Matrix.unitaryGroup (Bits (k * m)) ℂ :=
  (List.ofFn fun j => embedGate (e j) (c j).rep).prod

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
Definition 3.1, p.9: the two-layer Clifford ensemble `E2L` with block size `k` on `n = km`
qubits. A circuit is `U = U₂U₁`; layer `U₁` applies independent uniformly random `k`-qubit
Cliffords `C_0, …, C_{m−1}` to the contiguous blocks `{jk, …, jk+k−1}`; layer `U₂` applies
independent uniformly random Cliffords `C'_0, …, C'_{m−1}` to the same blocks shifted by `k/2`
qubits with periodic boundary conditions, `{jk + k/2 + i mod km : i < k}`.

**Formalization Note** The paper's `k` is an even divisor of `n`; here `n = k·m` by construction
and evenness of `k` is a hypothesis of each statement that needs it. A label is the pair of block
label vectors `(C, C')`, drawn uniformly, which is the same as independent uniform blocks. Cliffords
are drawn modulo global phase (`ShallowShadows.ShadowNorm.CliffordLabel`, whose finiteness is an
instance argument), and the unitary of a label is its representative; all quantities of the paper
depend on `U` only through `X ↦ U X U†`. For `m = 1` both layers act on all `k` qubits, the second
in the cyclically shifted qubit order, as the periodic boundary prescribes. Qubit `0` is the first
qubit of the register (`Bits n = Fin n → Fin 2`). -/
noncomputable def twoLayer (k m : ℕ) [Fintype (CliffordLabel k)] :
    Primitive (k * m) ((Fin m → CliffordLabel k) × (Fin m → CliffordLabel k)) where
  w := uniformDist _
  U c := blockLayer (blockEmb2 k m) c.2 * blockLayer (blockEmb1 k m) c.1

end ShadowBootstrap


