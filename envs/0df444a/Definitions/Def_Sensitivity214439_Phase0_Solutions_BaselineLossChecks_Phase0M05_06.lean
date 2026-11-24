-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossChecks_Phase0M05_06
-- name    : Sensitivity214439_Phase0_Solutions_BaselineLossChecks_Phase0M05_06
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:02:54.178497+00:00
-- url     : https://prove2.me/theorems/a1bef66f-6b37-4e68-9fed-1116ec31e879
-- title:
--   Integer dual table for unary loss at ranks $(5,6)$
-- statement:
--   For the unary Paley recipe and rank pair $(i,j)=(5,6)$, this bundle defines the fixed total lookup table
--
--   $$D_{5,6}:\mathbb{N}\longrightarrow\mathbb{N}\times\mathbb{Z}^5.$$
--
--   An entry consists of a denominator and five integer weights for socket multiplicity, guard checks, weak failures, strong failures, and the extra branch constraint. A local state with own heights $a,b$, failure counts $f_i,f_j$, and branch $b_0$ selects its entry using
--
--   $$\kappa(a,b,f_i,f_j,b_0)=2\bigl(8(8(12a+b)+f_i)+f_j\bigr)+b_0.$$
--
--   The table records the exact integer data for the baseline-loss certificate. Companion validity lemmas check the required signs, column domination, and total-cost inequality at every admissible state.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/BaselineLossChecks/Phase0M05_06.lean lines 8–84; SHA256 43bd8bc024179ed2cc66b000dbe57fd23ad9adb29399f52495b7bed1ffb4514c; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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

def phase0_mdual_5_6 (key : ℕ) : Dual :=
  if key < 14995 then
    if key < 13330 then
      if key < 13313 then
        if key < 11649 then
          if key = 11648 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 13312 then
            if key = 11649 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 13312 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 13314 then
          if key = 13313 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 13315 then
            if key = 13314 then ⟨83,3871099606942735802570811128427686602733518848,0,0,31282378363404544548801298056360851164333342720,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 13315 then ⟨83,3871099606942735802570811128427686602733518848,0,0,31282378363404544548801298056360851164333342720,0⟩ else ⟨1,0,0,0,0,0⟩
    else
      if key < 14977 then
        if key < 13331 then
          if key = 13330 then ⟨1,95039991749840130854986779666376877408256,0,61811380602039985147357555611446037150538137600,423440839169060766512182473278026849231831040,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 14976 then
            if key = 13331 then ⟨1,95039991749840130854986779666376877408256,0,61811380602039985147357555611446037150538137600,423440839169060766512182473278026849231831040,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 14976 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 14979 then
          if key < 14978 then
            if key = 14977 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 14978 then ⟨83,3871099606942735802570811128427686602733518848,0,0,31282378363404544548801298056360851164333342720,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 14994 then
            if key = 14979 then ⟨83,3871099606942735802570811128427686602733518848,0,0,31282378363404544548801298056360851164333342720,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 14994 then ⟨1,95039991749840130854986779666376877408256,0,61811380602039985147357555611446037150538137600,423440839169060766512182473278026849231831040,0⟩ else ⟨1,0,0,0,0,0⟩
  else
    if key < 16659 then
      if key < 16642 then
        if key < 16640 then
          if key = 14995 then ⟨1,95039991749840130854986779666376877408256,0,61811380602039985147357555611446037150538137600,423440839169060766512182473278026849231831040,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 16641 then
            if key = 16640 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 16641 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 16643 then
          if key = 16642 then ⟨1,95039991749840130854986779666376877408256,0,0,62234821441209045913869738084724063999769968640,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 16658 then
            if key = 16643 then ⟨83,3871099606942735802570811128427686602733518848,0,0,31282378363404544548801298056360851164333342720,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 16658 then ⟨1,95039991749840130854986779666376877408256,0,61811380602039985147357555611446037150538137600,423440839169060766512182473278026849231831040,0⟩ else ⟨1,0,0,0,0,0⟩
    else
      if key < 18306 then
        if key < 18304 then
          if key = 16659 then ⟨1,95039991749840130854986779666376877408256,0,61811380602039985147357555611446037150538137600,423440839169060766512182473278026849231831040,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 18305 then
            if key = 18304 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 18305 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 18322 then
          if key < 18307 then
            if key = 18306 then ⟨1,95039991749840130854986779666376877408256,0,0,62234821441209045913869738084724063999769968640,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 18307 then ⟨83,3871099606942735802570811128427686602733518848,0,0,31282378363404544548801298056360851164333342720,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 18323 then
            if key = 18322 then ⟨1,95039991749840130854986779666376877408256,0,61811380602039985147357555611446037150538137600,423440839169060766512182473278026849231831040,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 18323 then ⟨1,95039991749840130854986779666376877408256,0,61811380602039985147357555611446037150538137600,423440839169060766512182473278026849231831040,0⟩ else ⟨1,0,0,0,0,0⟩





end SensitivityBaselineLossNumeric


