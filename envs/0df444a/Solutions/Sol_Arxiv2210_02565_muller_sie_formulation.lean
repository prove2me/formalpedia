-- Prove2me | solution 1 for Arxiv2210_02565.muller_sie_formulation
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T20:54:28.300716+00:00
-- url     : https://prove2.me/submissions/850c7cc9-4c23-425f-864d-00f4d1958446

import Mathlib
import Definitions.Def_Arxiv2210_02565_Basic

open Filter Topology
open Arxiv2210_02565

lemma mu_curlE {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ω : ℝ) (ε μ k : ℂ) (hk : k ^ 2 = (ω : ℂ) ^ 2 * μ * ε)
    (curlOp : W →ₗ[ℂ] W) (S D : V →ₗ[ℂ] W)
    (hS : curlOp ∘ₗ S = D) (hD : curlOp ∘ₗ D = k ^ 2 • S) (u v : V) :
    curlOp (mullerE ω μ k S D u v) - (Complex.I * ω * μ) • mullerH ω ε k S D u v = 0 := by
  have a : curlOp (S v) = D v := LinearMap.congr_fun hS v
  have b : curlOp (D u) = k ^ 2 • S u := LinearMap.congr_fun hD u
  simp only [mullerE, mullerH, map_add, map_smul, a, b]
  have hI : (ω : ℂ) ^ 2 * μ * ε * Complex.I ^ 2 = -((ω : ℂ) ^ 2 * μ * ε) := by
    rw [Complex.I_sq]; ring
  linear_combination (norm := module) hk • D v + hI • D v

lemma mu_curlH {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ω : ℝ) (ε μ k : ℂ) (hk : k ^ 2 = (ω : ℂ) ^ 2 * μ * ε)
    (curlOp : W →ₗ[ℂ] W) (S D : V →ₗ[ℂ] W)
    (hS : curlOp ∘ₗ S = D) (hD : curlOp ∘ₗ D = k ^ 2 • S) (u v : V) :
    curlOp (mullerH ω ε k S D u v) + (Complex.I * ω * ε) • mullerE ω μ k S D u v = 0 := by
  have a : curlOp (S u) = D u := LinearMap.congr_fun hS u
  have b : curlOp (D v) = k ^ 2 • S v := LinearMap.congr_fun hD v
  simp only [mullerE, mullerH, map_add, map_sub, map_smul, a, b]
  have hI : (ω : ℂ) ^ 2 * μ * ε * Complex.I ^ 2 = -((ω : ℂ) ^ 2 * μ * ε) := by
    rw [Complex.I_sq]; ring
  linear_combination (norm := module) hk • D u + hI • D u

theorem solution {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (ω : ℝ) (hω : 0 < ω) (ε1 μ1 k1 ε2 μ2 k2 : ℂ)
    (hk1 : k1 ^ 2 = (ω : ℂ) ^ 2 * μ1 * ε1) (hk2 : k2 ^ 2 = (ω : ℂ) ^ 2 * μ2 * ε2)
    (curlOp : W →ₗ[ℂ] W) (S1 D1 S2 D2 : V →ₗ[ℂ] W)
    (hS1 : curlOp ∘ₗ S1 = D1) (hD1 : curlOp ∘ₗ D1 = k1 ^ 2 • S1)
    (hS2 : curlOp ∘ₗ S2 = D2) (hD2 : curlOp ∘ₗ D2 = k2 ^ 2 • S2)
    (T1 K1 T2 K2 : V →ₗ[ℂ] V) (trS1 trD1 trS2 trD2 : V →ₗ[ℂ] V)
    (hjS1 : trS1 = T1) (hjD1 : ∀ φ, trD1 φ = K1 φ + (1 / 2 : ℂ) • φ)
    (hjS2 : trS2 = T2) (hjD2 : ∀ φ, trD2 φ = K2 φ - (1 / 2 : ℂ) • φ)
    (u v M J : V) :
    (curlOp (mullerE ω μ1 k1 S1 D1 u v) - (Complex.I * ω * μ1) • mullerH ω ε1 k1 S1 D1 u v = 0 ∧
      curlOp (mullerH ω ε1 k1 S1 D1 u v) + (Complex.I * ω * ε1) • mullerE ω μ1 k1 S1 D1 u v = 0 ∧
      curlOp (mullerE ω μ2 k2 S2 D2 u v) - (Complex.I * ω * μ2) • mullerH ω ε2 k2 S2 D2 u v = 0 ∧
      curlOp (mullerH ω ε2 k2 S2 D2 u v) + (Complex.I * ω * ε2) • mullerE ω μ2 k2 S2 D2 u v = 0) ∧
    ((mullerTraceE ω μ2 k2 trS2 trD2 u v - mullerTraceE ω μ1 k1 trS1 trD1 u v = M ∧
        mullerTraceH ω ε2 k2 trS2 trD2 u v - mullerTraceH ω ε1 k1 trS1 trD1 u v = J) ↔
      mullerSIE ω ε1 μ1 k1 ε2 μ2 k2 T1 K1 T2 K2 u v = (M, J)) := by
  refine ⟨⟨mu_curlE ω ε1 μ1 k1 hk1 curlOp S1 D1 hS1 hD1 u v,
    mu_curlH ω ε1 μ1 k1 hk1 curlOp S1 D1 hS1 hD1 u v,
    mu_curlE ω ε2 μ2 k2 hk2 curlOp S2 D2 hS2 hD2 u v,
    mu_curlH ω ε2 μ2 k2 hk2 curlOp S2 D2 hS2 hD2 u v⟩, ?_⟩
  have e1 : mullerTraceE ω μ2 k2 trS2 trD2 u v - mullerTraceE ω μ1 k1 trS1 trD1 u v =
      (mullerSIE ω ε1 μ1 k1 ε2 μ2 k2 T1 K1 T2 K2 u v).1 := by
    simp only [mullerTraceE, mullerSIE, hjS1, hjS2, hjD1, hjD2]
    module
  have e2 : mullerTraceH ω ε2 k2 trS2 trD2 u v - mullerTraceH ω ε1 k1 trS1 trD1 u v =
      (mullerSIE ω ε1 μ1 k1 ε2 μ2 k2 T1 K1 T2 K2 u v).2 := by
    simp only [mullerTraceH, mullerSIE, hjS1, hjS2, hjD1, hjD2]
    module
  rw [e1, e2, Prod.ext_iff]

