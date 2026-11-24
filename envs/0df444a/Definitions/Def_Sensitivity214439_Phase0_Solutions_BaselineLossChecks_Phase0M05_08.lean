-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossChecks_Phase0M05_08
-- name    : Sensitivity214439_Phase0_Solutions_BaselineLossChecks_Phase0M05_08
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:02:51.686592+00:00
-- url     : https://prove2.me/theorems/7dd1a15a-f58b-4ec3-bb0e-020695b054e7
-- title:
--   Integer dual table for unary loss at ranks $(5,8)$
-- statement:
--   For the unary Paley recipe and rank pair $(i,j)=(5,8)$, this bundle defines the fixed total lookup table
--
--   $$D_{5,8}:\mathbb{N}\longrightarrow\mathbb{N}\times\mathbb{Z}^5.$$
--
--   An entry consists of a denominator and five integer weights for socket multiplicity, guard checks, weak failures, strong failures, and the extra branch constraint. A local state with own heights $a,b$, failure counts $f_i,f_j$, and branch $b_0$ selects its entry using
--
--   $$\kappa(a,b,f_i,f_j,b_0)=2\bigl(8(8(12a+b)+f_i)+f_j\bigr)+b_0.$$
--
--   The table records the exact integer data for the baseline-loss certificate. Companion validity lemmas check the required signs, column domination, and total-cost inequality at every admissible state.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/BaselineLossChecks/Phase0M05_08.lean lines 8–60; SHA256 880848c219681420c1e50ee9cbd1844f6a00c7651a300af4df76007ee375d49e; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossNumeric
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range

namespace SensitivityBaselineLossNumeric
end SensitivityBaselineLossNumeric



namespace SensitivityBaselineLossNumeric
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option Elab.async false

def phase0_mdual_5_8 (key : ℕ) : Dual :=
  if key < 16643 then
    if key < 14994 then
      if key < 14978 then
        if key < 14977 then
          if key = 14976 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key = 14977 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 14979 then
          if key = 14978 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key = 14979 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
    else
      if key < 16640 then
        if key < 14995 then
          if key = 14994 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key = 14995 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 16641 then
          if key = 16640 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 16642 then
            if key = 16641 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 16642 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
  else
    if key < 18305 then
      if key < 16659 then
        if key < 16658 then
          if key = 16643 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key = 16658 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 18304 then
          if key = 16659 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key = 18304 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
    else
      if key < 18307 then
        if key < 18306 then
          if key = 18305 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key = 18306 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 18322 then
          if key = 18307 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 18323 then
            if key = 18322 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 18323 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩





end SensitivityBaselineLossNumeric


