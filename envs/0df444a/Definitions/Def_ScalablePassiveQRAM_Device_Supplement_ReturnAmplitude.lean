-- Prove2me | Definitions.Def_ScalablePassiveQRAM_Device_Supplement_ReturnAmplitude
-- name    : ScalablePassiveQRAM_Device_Supplement_ReturnAmplitude
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:03:50.687775+00:00
-- url     : https://prove2.me/theorems/96543477-c2cd-477b-92e2-2f1efcaf4eec
-- title:
--   Return amplitudes of a sequence of dilated queries (setting of Fact 12)
-- statement:
--   The abstract setting of Fact 12. The algorithm's registers (address, bus, workspace and any reference purification) form a finite system $a$. After $k$ queries the device together with its environment is a finite system $e_k$; the environments may differ from query to query. Query $k$ ($k=1,\dots,m$) is an isometry $V_k:\mathcal H_a\otimes\mathcal H_{e_{k-1}}\to\mathcal H_a\otimes\mathcal H_{e_k}$, the idle states are unit vectors $|\xi_k\rangle\in\mathcal H_{e_k}$, the ideal query unitaries are $U_k$, and the algorithm applies channels $\Phi_0,\dots,\Phi_m$ on its own registers before, between and after the queries.
--
--   The module defines:
--
--   1. the **return-amplitude operator** $Z_k=(I\otimes\langle\xi_k|)\,V_k\,(I\otimes|\xi_{k-1}\rangle)$ on the algorithm's registers;
--   2. the **physical channel** $X\mapsto\operatorname{Tr}_{e_m}\big[(\Phi_m\otimes\mathrm{id})\circ\mathrm{Ad}_{V_m}\circ\cdots\circ\mathrm{Ad}_{V_1}\circ(\Phi_0\otimes\mathrm{id})\big](X\otimes|\xi_0\rangle\langle\xi_0|)$;
--   3. the **ideal channel** $\Phi_m\circ\mathrm{Ad}_{U_m}\circ\cdots\circ\mathrm{Ad}_{U_1}\circ\Phi_0$.
--
--   These are the objects compared in Fact 12, where the final error is the (unhalved) diamond distance between the physical and the ideal channel.
--
--   **Formalization Note** Indices are zero-based: query $k+1$ is `V k`, its overlap is `returnAmplitude V ξ k`, and data with index beyond $m$ is never used. $\Phi\otimes\mathrm{id}$ is written blockwise (`actLeft`), which is the tensor extension of a linear map.
-- source:
--   Siddhartha Jain, Alexander Dalzell, Connor Hann, STOC 2027 submission #129 (October 2026), §4.4, Fact 12, p. 32 (proof p. 33). Canonical PDF SHA256 725dff5ab83fbe7e163da05440b75cc1d24f83804408cc139eb8954d2f8a076e.

import Definitions.Def_ScalablePassiveQRAM_Device_Interfaces
import Mathlib

noncomputable section
open scoped BigOperators Matrix

namespace ScalablePassiveQRAM.Device.Supplement

/-! Abstract setting of Fact 12 (Jain–Dalzell–Hann, STOC 2027 #129, p. 32).

The algorithm's registers form a finite type `a`. After `k` queries the device together with
its environment is the finite type `env k`; the types may differ with `k`. Query `k+1`
(zero-based index `k`) is a rectangular matrix `V k : (a × env k) → (a × env (k+1))`,
`ξ k` is the idle vector of `env k`, `U k` is the ideal query and `Φ k` the channel the
algorithm applies on its own registers before query `k+1` (`Φ m` after the last query).
Data with index beyond the number of queries is never used. -/

/-- `(Φ ⊗ id_e)`: a map on the algorithm registers applied blockwise, leaving the device and
environment factor `e` (on the right) untouched, coherences included. -/
def actLeft {a e : Type} (Φ : Map a a) : Map (a × e) (a × e) :=
  fun X i j => Φ (fun p q => X (p, i.2) (q, j.2)) i.1 j.1

/-- The return-amplitude operator `Z_k = (I ⊗ ⟨ξ_k|) V_k (I ⊗ |ξ_{k-1}⟩)` of query `k+1`
(zero-based `k`): start the device and environment in `ξ k`, apply `V k`, and take the overlap
with `ξ (k+1)`. -/
def returnAmplitude {a : Type} {env : ℕ → Type} [∀ k, Fintype (env k)]
    (V : (k : ℕ) → Matrix (a × env (k+1)) (a × env k) ℂ) (ξ : (k : ℕ) → env k → ℂ) (k : ℕ) :
    Matrix a a ℂ :=
  fun i j => ∑ u : env (k+1), ∑ v : env k, star (ξ (k+1) u) * V k (i, u) (j, v) * ξ k v

/-- Joint state of algorithm registers and device-plus-environment after `k` queries and the
channel that follows them: `Φ_k ∘ Ad V_k ∘ ⋯ ∘ Ad V_1 ∘ Φ_0` applied to `X ⊗ |ξ_0⟩⟨ξ_0|`. -/
def physicalPrefix {a : Type} [Fintype a] {env : ℕ → Type} [∀ k, Fintype (env k)]
    [DecidableEq a]
    (V : (k : ℕ) → Matrix (a × env (k+1)) (a × env k) ℂ) (ξ : (k : ℕ) → env k → ℂ)
    (Φ : ℕ → WildeQIT.QChannel a a) : (k : ℕ) → Map a (a × env k)
  | 0 => fun X => tensor ((Φ 0).apply X) (outer (ξ 0) (ξ 0))
  | k+1 => fun X => actLeft (Φ (k+1)).apply (conjugate (V k) (physicalPrefix V ξ Φ k X))

/-- The physical `m`-query channel on the algorithm's registers: the device and environment
start in `ξ 0`, the queries are the `V k`, the algorithm applies `Φ k` between queries, and
the device and environment are traced out at the end. -/
def physicalChannel {a : Type} [Fintype a] {env : ℕ → Type} [∀ k, Fintype (env k)]
    [DecidableEq a]
    (V : (k : ℕ) → Matrix (a × env (k+1)) (a × env k) ℂ) (ξ : (k : ℕ) → env k → ℂ)
    (Φ : ℕ → WildeQIT.QChannel a a) (m : ℕ) : Map a a :=
  fun X => WildeQIT.partialTraceRight (physicalPrefix V ξ Φ m X)

/-- The ideal `m`-query channel `Φ_m ∘ Ad U_m ∘ ⋯ ∘ Ad U_1 ∘ Φ_0`. -/
def idealChannel {a : Type} [Fintype a] [DecidableEq a]
    (U : ℕ → Matrix a a ℂ) (Φ : ℕ → WildeQIT.QChannel a a) : ℕ → Map a a
  | 0 => fun X => (Φ 0).apply X
  | k+1 => fun X => (Φ (k+1)).apply (conjugate (U k) (idealChannel U Φ k X))

end ScalablePassiveQRAM.Device.Supplement


